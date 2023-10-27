from copy import copy
import os.path
import re
import time
import warnings
from typing import List, SupportsFloat, Any, Tuple, Dict
from func_timeout import func_set_timeout
import grpc

import requests
import json

import gymnasium as gym
from gymnasium.core import ObsType

import lego_prover.utils as U

from .process_monitor import SubprocessMonitor

import lego_prover.env.server_pb2 as server_pb2
import lego_prover.env.server_pb2_grpc as server_pb2_grpc

import logging

MAX_MESSAGE_LENGTH = 10485760

SPECIAL_SYMBOL = {
    "≥": "\<ge>",
    "≤": "\<le>",
    "≠": "\<noteq>",
    "∧": "\<and>",
    "∨": "\<or>",
    "¬": "\<not>",
    "⇒": "\<Rightarrow>",
    "⇔": "\<longleftrightarrow>",
    "→": "\<longrightarrow>",
    "∀": "\<forall>",
    "∃": "\<exists>",
    "∈": "\<in>",
    "⊆": "\<subseteq>",
    "∪": "\<union>",
    "∩": "\<inter>",
    "⊂": "\<subset>",
    "∅": "\<emptyset>",
    "∑": "\<sum>",
    "∫": "\<integral>",
    "≡": "\<equiv>",
    "⊢": "\<turnstile>",
    "⊨": "\<models>",
    "⊥": "\<bottom>",
    "⊤": "\<top>",
    "≜": "\<triangleq>",
    "≈": "\<approx>",
    "≅": "\<cong>",
    "⋀": "\<And>",
    "⋁": "\<Or>",
    "⋂": "\<Inter>",
    "⋃": "\<Union>",
    "⊗": "\<otimes>",
    "∗": "\<star>",
    "λ": "\<lambda>",
    "∞": "\<infinity>",
    "ℕ": "\<nat>",
    "ℤ": "\<int>",
    "ℚ": "\<rat>",
    "ℝ": "\<real>",
    "ℂ": "\<complex>",
    "↔": "\<leftrightarrow>",
    "‹": "\<open>",
    "›": "\<close>",
    "α": "\<alpha>",
    "β": "\<beta>",
    "γ": "\<gamma>",
 
    # "𝑎": "a",
    # "¯": "?",
    # "∤": "?",
    "sorry": "sledgehammer",
    "oops": "sledgehammer",
}

def create_stub(port=9000):
    channel = grpc.insecure_channel('localhost:{}'.format(port),
                                    options=[('grpc.max_send_message_length', MAX_MESSAGE_LENGTH),
                                             ('grpc.max_receive_message_length', MAX_MESSAGE_LENGTH)])
    return server_pb2_grpc.ServerStub(channel)


class IsabelleEnv(gym.Env):
    def __init__(
        self,
        logger=None,
        isabelle_path="/Users/wiio/Isabelle2022",
        working_dir="miniF2F",
        interactive_file="miniF2F/interactive.thy",
        server_host="http://127.0.0.1",
        server_port=8000,
        request_timeout=600,
        log_path="./logs",
    ):
        self.logger = logger
        self.isabelle_path = isabelle_path
        self.working_dir = os.path.abspath(working_dir)
        self.interactive_file = os.path.abspath(interactive_file)
        self.server = f"{server_host}:{server_port}"
        self.server_port = server_port
        self.request_timeout = request_timeout
        self.log_path = log_path
        self.isabelle_server = self.get_isabelle_process(server_port)
        self.isabelle_server.run()
        self.stub = None
        
        # wait for isabelle server to run
        time.sleep(3)

        self.has_reset = False
        self.reset_options = None
        self.connected = False

    def get_isabelle_process(self, server_port):
        self.logger.info(f"Starting isabelle server at port {server_port}")
        U.f_mkdir(self.log_path, "isabelle_server")
        return SubprocessMonitor(
            commands=[
                "bash",
                "run_server.sh",
                str(server_port),
            ],
            name="isabelle_server",
            ready_match=r"Server is running. Press Ctrl-C to stop.",
            log_path=U.f_join(self.log_path, "isabelle_server"),
            cwd=os.path.abspath("lego_prover/env/Portal-to-ISAbelle"),
            server_port=server_port,
        )
        
    def step(
        self,
        code: str,
        formal_statement: str = None,
        quick_check: bool = False,
    ) -> Tuple[ObsType, SupportsFloat, bool, bool, Dict[str, Any]]:
        # if "theory" in code:
        #     assert "begin" in code and "end" in code, \
        #         "Outer syntax error: not complete theorem file"
        #     code = code[code.index("begin") + len("begin"): code.index("end")].strip()
        
        # step 0: replace special token
        for symbol, value in SPECIAL_SYMBOL.items():
            if symbol in code:
                code = code.replace(symbol, value)

        # step 1: parse code
        parsed_code = self._get_parsed_code(code)

        # step 2: step by step verification
        verified_result = self._verify_step_by_step(parsed_code, quick_check=quick_check)
        if quick_check:
            return verified_result, None, None, None

        # step 3: post process error message
        verified_result, code, correct_partial_code, incorrect_code = self._post_process_error_msg(code, parsed_code, verified_result)

        # step 4: get skill code
        skill_codes = self._post_process_skill_code(correct_partial_code)

        # step 5: get request
        requests = self._get_request(code, skill_codes)
        
        return verified_result, code, skill_codes, requests

    def render(self):
        raise NotImplementedError("render is not implemented")

    def reset(self, imports=None, hard_reset=False):
        # TODO: we fix the imports for now, we support update imports later.
        if self.stub is None or hard_reset:
            self.stub = create_stub(self.server_port)
            try:
                self.logger.info(self.stub.InitialiseIsabelle(server_pb2.IsaPath(path=self.isabelle_path)).message)
                self.logger.info(self.stub.IsabelleWorkingDirectory(server_pb2.IsaPath(path=self.working_dir)).message)
                self.logger.info(self.stub.IsabelleContext(server_pb2.IsaContext(context=self.interactive_file)).message)
                self.successful_starting = True
            except Exception as e:
                self.logger.info("Failure at initializing Isabelle process.\n"
                      "Make sure the path your provide is where the Isabelle executable is.")
                self.logger.info(e)
            # This will reset all state
            self._post(f"<initialise>")
            return f"Starting is successful: {self.successful_starting}"
        else:
            self._post("reset_problem")
            return f"soft reset problem successful"
    
    def close(self):
        if self.stub is not None:
            self._exit()
        self.isabelle_server.stop()
        return not self.connected
    
    # @func_set_timeout(1800, allowOverride=True)
    def _post(self, action):
        reset_retry_cnt = 3
        while reset_retry_cnt > 0:
            try:
                result = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=action)).state
                return result
            except Exception as e:
                self.logger.info(f"Isabelle environment exception: {e}")
                self.isabelle_server.terminate()
                self.isabelle_server = self.get_isabelle_process(self.server_port)
                self.isabelle_server.run()
                time.sleep(3)
                self.reset(hard_reset=True)
                reset_retry_cnt -= 1
        assert False, "Isabelle enviroment fail to reboot!"
            

    def _exit(self):
        try:
            self._post('exit')
        except:
            self.logger.info("Post('exit') timed out, kill from system...")
            os.system("ps aux | grep Isabelle | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")
            os.system("ps aux | grep poly | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")


    def _get_parsed_code(self, theory, tls_name='default') -> List[str]:
        steps = self._post(f"<parse text> ${theory}")
        steps = steps.split('<SEP>')
        steps = [s for s in steps if s.strip() != '']
        # remove weird '$' step and whitespace steps
        steps = [s for s in steps if s != '$' and s.strip() != '']
        return steps
    
    def _parse_hammer_output(self, obs):
        """Parse the sledgehammer output, otherwise return an empty string"""
        if '<hammer>' in obs:
            output = obs.split('<hammer>')[1]
        else:
            output = ''
        return output

    def _verify_step_by_step(self, steps, quick_check=False):
        done = False
        reason = ''
        success = False
        step_results = []
        tls_name = 'default'
        error_step_index = None
        corrected_step = {}
        for i, step in enumerate(steps):
            try:
                step_time = time.time()
                if "sledgehammer" not in step:
                    obs, reward, done, metadata, error = self._run_step(step, i, tls_name)
                    strip_step = step.strip()

                    if error is not None and quick_check is True:
                        self._post("reset_problem")
                        return False
                    
                    # only fix "by" step
                    if error is not None and strip_step.startswith("by"):
                        old_status = copy((obs, reward, done, metadata, error))
                        # try correct the step with sledgehammer step
                        one_line_error = error.replace('\n', ' ')
                        self.logger.info(f"Error with step: [{step}], error: [{one_line_error}]")
                        self.logger.info("Trying hammer methods...")
                        obs, reward, done, metadata, error = self._run_sledgehammer(step, i, tls_name)
                        if obs is not None:
                            actual_step, obs = obs.split("<hammer>")
                            actual_step, obs = actual_step.strip(), obs.strip()
                            corrected_step[i] = (step, actual_step)
                        else:
                            obs, reward, done, metadata, error = old_status
                else:
                    if quick_check is True:
                        self._post("reset_problem")
                        return False
                    self.logger.info("Model use sledgehammer, Trying hammer methods...")
                    obs, reward, done, metadata, error = self._run_sledgehammer(step, i, tls_name)
                    if obs is not None:
                        actual_step, obs = obs.split("<hammer>")
                        actual_step, obs = actual_step.strip(), obs.strip()
                        corrected_step[i] = (step, actual_step)

                step_time = time.time() - step_time
                step_results.append({
                    "index": i,
                    "step": step,
                    "output": obs,
                    "step_time": step_time,
                })
                if error is not None:
                    reason = error
                    success = False
                    done = False
                    error_step_index = i
                    break
            except Exception as e:
                # Timeout - end the proof attempt
                success = False
                done = False
                reason = f'Python exception with error {str(e)}, at command "{step}" (line 1)'
                error_step_index = i
                step_results.append(dict(index=i, step=step, output=''))
                break

            # Change when successful
            tls_name = 'default_%d' % i

        if done and reward == 1.0:
            success = True

        result = {
            'success': success,
            'reason': reason,
            'num_steps': len(steps),
            'last_step': len(step_results),
            'error_step_index': error_step_index,
            'step_results': step_results,
            'corrected_steps': corrected_step,
        }

        # This will reset all the problem status
        self._post("reset_problem")
        if quick_check is True:
            return success
        return result

    def _run_sledgehammer(self, step, i, tls_name):
        # First try heuristics
        for heuristic in ['by auto', 'by simp', 'by blast', 'by fastforce', 'by force', 'by eval', 'by presburger', 'by sos', 'by arith', 'by linarith', 'by (auto simp: field_simps)', "sledgehammer"]:
            step_ = heuristic
            obs, reward, done, metadata, error = self._run_step(step_, i, tls_name)            
            if error is None:
                if "<hammer>" not in obs:
                    obs = '%s <hammer> %s' % (heuristic, obs)
                actual_step = obs.split("<hammer>")[0].strip()
                self.logger.info(f"Tried step: {step_}, success, replace step: [{step}] with step: [{actual_step}]")
                return obs, reward, done, metadata, error
            else:
                if step_ == "sledgehammer":
                    one_line_error = error.replace('\n', ' ')
                    self.logger.info(f"Tried step: {step_} with error [{one_line_error}]")
                    if 'At command "<malformed>"' in one_line_error:
                        error = "Sledgehammer error (line 1): fail to finish the proof with sledgehammer"
                    return None, reward, done, metadata, error
        # Try sledgehammer
        # if error.replace('\n', ' ').startswith("Step error: Outer syntax error (line 1): command expected"):
        #     error = "Sledgehammer error (line 1): fail to finish the proof with sledgehammer"
        return obs, reward, done, metadata, error

    def _run_step(self, step, i, tls_name):
        obs, reward, done, metadata = self.step_to_top_level_state(
            action=step,
            tls_name=tls_name,
            new_name='default_%d' % i
        )
        error = None
        if 'error:' in obs or 'Step error' in obs or 'Unknown error' in obs:
            error = obs
        return obs, reward, done, metadata, error

    def step_to_top_level_state(self, action, tls_name, new_name):
        # last_obs_string = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=f"<get state> {tls_name}")).state
        obs_string = "Step error"
        try:
            obs_string = self._post(f"<apply to top level state> {tls_name} <apply to top level state> {action} <apply to top level state> {new_name}")
            # print(obs_string)
        except Exception as e:
            self.logger.info("***Something went wrong***")
            self.logger.info(e)

        if "error" in obs_string:
            done = False
        else:
            done = self.is_finished(new_name)
        # done = True if ("subgoal" in last_obs_string and "subgoal" not in obs_string) else False
        return obs_string, self.reward(done), done, {}

    def reward(self, done):
        return 1 if done else 0

    def is_finished(self, name_of_tls):
        ret = self._post(f"<is finished> {name_of_tls}").strip()
        return ret.startswith("t")
    
    def get_marker_statement(self, code):
        parsed = self._get_parsed_code(code)
        sl = []
        for code in parsed:
            code = code.strip()
            if code.startswith("lemma") or code.startswith("theorem") or code.startswith("fun") or code.startswith("definition"):
                sl.append(code)
        return sl[-1]

    
    def _post_process_error_msg(self, code, parsed_code, verified_result):
        old_code = copy(code)
        only_refresh_code = False
        if "Timeout after" in verified_result["reason"]:
            verified_result["reason"] = \
            'Step timeout error (line 1): the step takes more than 10 seconds to run. At command "<cmd>" (line 1)'
        if verified_result["success"] is True:
            only_refresh_code = True
        elif re.search(r"\(line [0-9]+\)", verified_result["reason"]) is None and \
            re.search(r'At command "(.?)+"', verified_result["reason"]) is None:
            self.logger.info("No line number or at command, skip...")
            self.logger.info("The error is:")
            self.logger.info(verified_result["reason"])
            only_refresh_code = True
        
        matched_codes = []
        for ix, step in enumerate(verified_result["step_results"]):
            step_code = step["step"].strip()
            if step_code not in code:
                # This error is too complicated, I give up
                if len(step["output"]) != 0:
                    return verified_result, old_code, "".join(matched_codes), code
                else:
                    if step_code.startswith("(*"):
                        start_index = code.index("(*")
                        self.logger.info(f"Parsed code: {step_code}")
                        self.logger.info(f"ori code: {code}")
                        for i in range(len(step_code)):
                            if code[i+start_index] != step_code[i]:
                                assert step_code[i] == "?"
                                code = code[:i+start_index] + step_code[i] +  code[i+start_index+1:]
                        self.logger.info(f"new code: {code}")
                    else:
                        self.logger.info(f"Parsed code: {step_code}")
                        self.logger.info(f"ori code: {code}")
                        assert False, "You should add the list!"
            new_step = None
            if ix in verified_result["corrected_steps"]:
                old_step, new_step = verified_result["corrected_steps"][ix]
                assert old_step == step_code
            matched_code = code[:code.index(step_code) + len(step_code)]
            code = code[code.index(step_code) + len(step_code):]
            if new_step is not None:
                matched_code = matched_code.replace(step_code.strip(), new_step.strip())
            matched_codes.append(matched_code)
        
        correct_code = "".join(matched_codes)
        incorrect_code = code

        if not only_refresh_code:
            previous_code = "".join(matched_codes)
            line_number = previous_code.strip().count("\n") + 1

            error_msg = re.sub(r"\(line [0-9]+\)", f"(line {line_number})", verified_result["reason"])
            error_msg = re.sub(r'At command "(.?)+"', f'At command "{repr(step_code)}"', error_msg)

            verified_result["reason"] = error_msg
        
        new_code = "".join(matched_codes + [code])

        return verified_result, new_code, correct_code, incorrect_code
    
    def get_lemma_name(self, code):
        name = "no_name"
        try:
            if code.startswith('lemma'):
                name = re.findall(r"lemma (.+):", code)[0].strip()
            elif code.startswith('theorem'):
                name = re.findall(r"theorem (.+):", code)
                if len(name) == 0:
                    name = "theorem_with_no_name"
                else:
                    name = name[0].strip()
            elif code.startswith('fun') and not code.startswith('function'):
                name = re.findall(r"fun (.+) ::", code)[0].strip()
            elif code.startswith('function'):
                name = re.findall(r"function (.+) ::", code)[0].strip()
            elif code.startswith('definition'):
                name = re.findall(r"definition (.+) ::", code)[0].strip()
            else:
                assert False, f"new code type: {code}"
        except Exception as e:
            self.logger.info(f"Error get lemma name, error: {e}, code: {code}")
        return name
    
    def _post_process_skill_code(self, correct_partial_code):
        start_keyword = ["lemma", "theorem", "definition", "fun", "end"]
        
        parsed_code = self._get_parsed_code(correct_partial_code)
        all_codes = []
        current_code_set = []
        for code in parsed_code:
            if code.startswith(tuple(start_keyword)):
                if len(current_code_set) > 0:
                    skill_code = "\n".join(current_code_set)
                    all_codes.append(skill_code.strip())
                current_code_set = [code]
            else:
                assert len(all_codes) == 0 or len(current_code_set) > 0
                if len(current_code_set) != 0:
                    current_code_set.append(code)
        
        # remove empty code:
        tmp_code = []
        for code in all_codes:
            code = self._beautify(code, correct_partial_code)
            if len(code) == 0:
                continue
            tmp_code.append(code)
        all_codes = tmp_code

        # resolve dependence
        all_names = []
        for code in all_codes:
            all_names.append(self.get_lemma_name(code))
        
        name_and_codes = list(zip(all_names, all_codes))
        name_and_codes = sorted(name_and_codes, key=lambda x: len(x[0]), reverse=True)
        if len(name_and_codes) > 0:
            all_names, all_codes = list(zip(*name_and_codes))
        else:
            all_names, all_codes = [], []
        
        new_codes = []
        for ix, code in enumerate(all_codes):
            current_code = code
            escape_names = [all_names[ix]]
            while True:
                updated = False
                for jx, name in enumerate(all_names):
                    if name in escape_names:
                        continue
                    if name in current_code:
                        current_code = f"{all_codes[jx]}\n\n{current_code}"
                        escape_names.append(name)
                        updated = True
                if updated is False:
                    break
            new_codes.append(current_code)
        
        return list(zip(all_codes, new_codes))

    def _beautify(self, ori_code, correct_partial_code):
        parsed_code = self._get_parsed_code(ori_code)
        if ori_code.startswith("lemma") or ori_code.startswith("theorem"):
            if len(parsed_code) <= 1:
                return ""
        else:
            return ori_code
        if parsed_code[0].strip() not in correct_partial_code:
            return ori_code

        formatted_code = correct_partial_code[correct_partial_code.index(parsed_code[0]):]
        matched_codes = []
        for ix, step_code in enumerate(parsed_code):
            step_code = step_code.strip()
            if step_code not in formatted_code:
                # This error is too complicated, I give up
                return ori_code
            matched_code = formatted_code[:formatted_code.index(step_code) + len(step_code)]
            formatted_code = formatted_code[formatted_code.index(step_code) + len(step_code):]
            matched_codes.append(matched_code)
        
        new_code = "".join(matched_codes)
        
        # remove all the comments
        # This regular expression pattern will find all comments in the Isabelle code
        pattern = re.compile(r"\(\*(.*?)\*\)", re.DOTALL)

        # Substitute found comments with an empty string
        new_code = re.sub(pattern, '', new_code).strip()
        new_code = '\n'.join(line for line in new_code.splitlines() if line.strip())

        if len(self._get_parsed_code(new_code)) <= 1:
            return ""
        return new_code

    def _get_request(self, code, skill_codes):
        parsed = self._get_parsed_code(code)
        requests = []
        for line in parsed:
            if line.strip().startswith("lemma"):
                requests.append(line)
        full_codes = [k[1] for k in skill_codes]
        full_code = "\n\n".join(full_codes)
        requests = list(filter(lambda x: x not in full_code, requests))
        return requests





if __name__ == "__main__":
    import logging 
    logger = logging.getLogger()
    env = IsabelleEnv(logger=logger, isabelle_path="/data1/wanghaiming/Isabelle2022/")
    env.reset()
    code = r"""
theory Scratch
imports Main
begin

lemma sum_induction:
  fixes a b n :: nat
  assumes "a > 0" "b > 0" "(\Sum>k = 0..n. a * k + b) = n^2 * a + 2 * n * a + b"
  shows "(\Sum>k = 0..Suc n. a * k + b) = (n+1)^2 * a + 2 * (n+1) * a + b"
proof -
  have "(\<Sum>k = 0..Suc n. a * k + b) = (\Sum>k = 0..n. a * k + b) + a * (n+1) + b" by simp
  also have "... = n^2 * a + 2 * n * a + b + a * (n+1) + b" using assms(3) by simp
  also have "... = (n+1)^2 * a + 2 * (n+1) * a + b" by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed


theorem induction_sum_odd:
  fixes n :: nat
  assumes "n > 0"
  shows "(\<Sum>(k::nat) = 0..(n-1). 2 * k + 1) = n^2"
proof (induct n)
  case 0
  then show ?case using assms by simp
next
  case (Suc n)
  then have "(\<Sum>k = 0..Suc n - 1. 2 * k + 1) = n^2 + 2 * n + 1" using sum_induction[of 2 1 n] Suc.hyps by simp
  also have "... = (Suc n)^2" by (simp add: power2_eq_square algebra_simps)
  finally show ?case .
qed

end
    """
    verified_result, code, skill_codes = env.step(code)
    print(f"####### Success: {verified_result['success']} ########")
    print("##### output ########")

    print(code)
    
    