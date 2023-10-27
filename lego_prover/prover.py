import os
import random
import re
import time
import multiprocessing as mp
import tiktoken
from lego_prover.env.isa_bridge import IsabelleEnv

import lego_prover.utils as U

from .agents import ActionAgent
from .agents import CurriculumAgent
from .agents import SkillManager
from langchain.schema import HumanMessage

import logging


class Prover:
    def __init__(
        self,
        rank: int = None,
        isabelle_path: str = None,
        server_port: int = 8000,
        model_name: str = "gpt-4",
        temperature: int = 0,
        action_agent_task_max_retries: int = 4,
        curriculum_task_type: str = "simple_curriculum",
        curriculum_agent_lock = U.WithEmpty(),
        skill_manager_lock = U.WithEmpty(),
        chroma_bridge = None,
        openai_api_request_timeout: int = 6000,
        ckpt_dir: str = "ckpt",
        resume: bool = False,
        miniF2F_tasks: mp.Queue = None,
    ):
        """
        Initializes a new instance of the Prover class.

        Args:
            rank (int): The rank of the prover process.
            isabelle_path (str): The path to the Isabelle directory.
            server_port (int): The port number for the server.
            model_name (str): The name of the OpenAI model to use.
            temperature (int): The temperature for sampling the LLM.
            action_agent_task_max_retries (int): The maximum number of retries for an action agent task.
            curriculum_task_type (str): The type of curriculum task to use.
            curriculum_agent_lock: The lock for the curriculum agent.
            skill_manager_lock: The lock for the skill manager.
            chroma_bridge: The ChromaBridge object for controlling the keyboard and mouse.
            openai_api_request_timeout (int): The timeout for OpenAI API requests.
            ckpt_dir (str): The directory for saving checkpoints.
            resume (bool): Whether to resume from the checkpoint.
            miniF2F_tasks (mp.Queue): The queue for miniF2F tasks.
        """

        # init env
        self.rank = rank
        self.logger = logging.getLogger(f'prover-{rank}')
        self.logger.info(f"lego_prover running in rank {rank}")
        self.model_name = model_name

        self.env = IsabelleEnv(
            logger=self.logger,
            isabelle_path=isabelle_path,
            server_port=server_port
        )
        self.action_agent_model_name = model_name
        self.tokenizer_encoder = tiktoken.encoding_for_model(
            self.action_agent_model_name)

        self.ckpt_dir = ckpt_dir
        self.temperature = temperature

        # init agents
        self.action_agent = ActionAgent(
            logger=self.logger,
            model_name=model_name,
            temperature=temperature,
            request_timeout=openai_api_request_timeout,
            ckpt_dir=ckpt_dir,
        )
        self.action_agent_task_max_retries = action_agent_task_max_retries
        self.curriculum_agent = CurriculumAgent(
            logger=self.logger,
            ckpt_dir=ckpt_dir,
            resume=resume,
            miniF2F_tasks=miniF2F_tasks,
            curriculum_task_type=curriculum_task_type,
            curriculum_agent_lock=curriculum_agent_lock,
        )
        self.skill_manager = SkillManager(
            rank=rank,
            logger=self.logger,
            ckpt_dir=ckpt_dir,
            skill_manager_lock=skill_manager_lock,
            chroma_bridge=chroma_bridge,
        )
        self.resume = resume

        # init variables for rollout
        self.action_agent_rollout_num_iter = -1
        self.task = None
        self.context = ""
        self.messages = None
        self.conversations = []
        self.last_events = None

    def _fill_skills(self, retrieved_skills, requested_skills, n_retrieved, n_requested, model_name):
        """
        Given the retrieved skills query by problem statement and requests, output `n_retrieved + n_requested`
        skill examples.
        """
        if model_name == "gpt-4":
            raise NotImplementedError

        skills = random.sample(retrieved_skills, min(n_retrieved, len(self.retrieved_skills))) + \
            random.sample(requested_skills, min(
                n_requested, len(self.requested_skills)))

        skill_names = [skill["skill"] for skill in skills]
        n_skill = n_retrieved + n_requested
        if len(skills) < n_skill:
            for s in requested_skills:
                if len(skills) == n_skill:
                    break
                if s["skill"] not in skill_names:
                    skills.append(s)
            for s in retrieved_skills:
                if len(skills) == n_skill:
                    break
                if s["skill"] not in skill_names:
                    skills.append(s)
        self.logger.info(f"There are {len(skills)} in total")
        return skills

    def reset(self, task, context, reset_env=True):
        self.context = context
        self.action_agent_rollout_num_iter = 0
        self.task = task
        if reset_env:
            self.env.reset()

        self.retrieved_skills = self.skill_manager.retrieve_skills_with_context(
            context=context)
        self.informal_proof, skill_requests, conversation = self.action_agent.decomposer(
            context=context,
        )
        self.info = {"decomposer_conversation": conversation}
        for request in skill_requests:
            request_name = self.env.get_lemma_name(request)
            self.logger.info(
                f"adding request: name: {request_name}, code: {request}")
            self.skill_manager.add_new_request(
                problem_name=task, formal_statement=request, init_update_count=0)

        # request skill
        self.requested_skills = []
        requested_skills_name = [s["skill"] for s in self.retrieved_skills]
        for skill_context in skill_requests:
            name = self.env.get_lemma_name(skill_context)
            query = f"code: {skill_context}, skill: {name}"
            requested_skill = self.skill_manager.retrieve_skills(query, 2)
            self.logger.info(
                f"Skill request query: {query} with result {requested_skill}")
            for rskill in requested_skill:
                if rskill["skill"] not in requested_skills_name:
                    requested_skills_name.append(rskill["skill"])
                    self.requested_skills.append(rskill)
        self.logger.info(
            f"There are {len(skill_requests)} with result of {len(self.requested_skills)} requested skill retrieved")

        system_message = self.action_agent.render_formalizer_system_message()
        skills = self._fill_skills(
            self.retrieved_skills, self.requested_skills, 0, 4, self.model_name)

        human_message = self.action_agent.render_formalizer_human_message(
            skills=skills, context=context, informal_proof=self.informal_proof, n_example=2
        )
        self.messages = [system_message, human_message]
        self.logger.info(
            f"****formalizer system message****\n{system_message.content}"
        )
        assert len(self.messages) == 2
        self.conversations = []
        self.history_messages = []
        return self.messages

    def close(self):
        self.env.close()

    def step(self):
        if self.action_agent_rollout_num_iter < 0:
            raise ValueError("Agent must be reset before stepping")
        skill_codes = []

        conversation = {"action_agent_sys0": self.messages[0].content,
                        "action_agent_human0": self.messages[1].content}
        # query model
        n_retry = 3
        while n_retry > 0:
            try:
                self.logger.info(
                    f"****formalizer human message****\n{self.messages[-1].content}"
                )
                ai_message = self.action_agent.llm(
                    self.messages, temperature=self.temperature, max_tokens=2000)
                conversation[f"action_agent_ai{3 - n_retry}"] = ai_message.content
                self.logger.info(
                    f"****formalizer ai message****\n{ai_message.content}")
                # text = ai_message.content[ai_message.content.index("# Formalized code"):]
                text = ai_message.content
                if "####################" in text:
                    text = text[:text.index("####################")]
                code_pattern = re.compile(
                    r"```(?:[i|I]sabelle)(.*?)```", re.DOTALL)
                parsed_result = "\n".join(code_pattern.findall(text)).strip()
                assert self.context["formal_statement"] in parsed_result, \
                    "Formal statement is not in the formal code generated"
                break
            except AssertionError as e:
                if "query too long" in str(e):
                    self.logger.info(str(e))
                    parsed_result = False
                    context_length = len(self.messages[1].content)
                    self.messages[1] = HumanMessage(
                        content=self.messages[1].content[int(context_length * 0.3):])
                    n_retry -= 1
                    conversation[f"formalizer{3 - n_retry}"] = self.messages[1].content
                else:
                    self.logger.info(f"parse failed with error: {str(e)}")
                    parsed_result = False
                    skills = self._fill_skills(
                        self.retrieved_skills, self.requested_skills, 0, 4, self.model_name)
                    human_message = self.action_agent.render_formalizer_human_message(
                        skills=skills, context=self.context, informal_proof=self.informal_proof, n_example=2
                    )
                    n_retry -= 1
                    conversation[f"formalizer{3 - n_retry}"] = self.messages[1].content
                    self.messages[1] = human_message
            except Exception as e:
                self.logger.info(f"parse failed with error: {str(e)}")
                parsed_result = False
                skills = self._fill_skills(
                    self.retrieved_skills, self.requested_skills, 0, 4, self.model_name)
                human_message = self.action_agent.render_formalizer_human_message(
                    skills=skills, context=self.context, informal_proof=self.informal_proof, n_example=2
                )
                n_retry -= 1
                conversation[f"formalizer{3 - n_retry}"] = self.messages[1].content
                self.messages[1] = human_message
                time.sleep(5)

        self.history_messages += [self.messages[1], ai_message]
        self.conversations.append(
            (self.messages[0].content,
             self.messages[1].content, ai_message.content)
        )
        if isinstance(parsed_result, str):
            self.logger.info("*******Parse success, verifying result*******")
            verified_result, parsed_result, skill_codes, requests = self.env.step(
                parsed_result, formal_statement=self.context["formal_statement"])
            self.logger.info(f'Success: {verified_result["success"]}')
            self.logger.info(f'Error: {verified_result["reason"]}')
            if len(requests) > 10:
                self.logger.warn(
                    f"Too many request! with {len(requests)} in total")
                requests = random.sample(requests, 10)
            for req in requests:
                self.skill_manager.add_new_request(
                    problem_name=self.task,
                    formal_statement=req,
                    init_update_count=-3,
                )
        else:
            assert isinstance(parsed_result, bool)
            self.logger.warn(f"{parsed_result} Trying again!")
            verified_result = {"success": False}
        assert len(self.messages) == 2
        self.action_agent_rollout_num_iter += 1
        done = True
        info = {
            "task": self.task,
            "success": verified_result["success"],
            "conversations": self.conversations,
            "code": parsed_result,
            "context": self.context,
            "verified_result": verified_result,
            "action_agent_conversation": conversation
        }
        self.info.update(info)
        return self.messages, 0, done, self.info, skill_codes

    def rollout(self, *, task, context, reset_env=True, gt_formal_code=None):
        all_skill_codes = []
        self.reset(task=task, context=context, reset_env=reset_env)
        while True:
            messages, reward, done, info, skill_codes = self.step()
            all_skill_codes.extend(skill_codes)
            if done or gt_formal_code is not None:
                break

        if info["success"] is True:
            self.logger.info("########## Final result ##########")
            self.logger.info(f'{info["code"]}')
            self.logger.info("##################################")
        else:
            self.logger.info("########## Final result ##########")
            self.logger.info('sad!!!!!')
            self.logger.info("##################################")

        # -- deduplicate according to the marker
        if len(all_skill_codes) > 0:
            markers, full_codes = list(zip(*all_skill_codes))
            dedup_set = set()
            all_skill_codes = []
            for ix, marker in enumerate(markers):
                if marker in dedup_set:
                    continue
                dedup_set.add(marker)
                all_skill_codes.append([marker, full_codes[ix]])

        if len(all_skill_codes) > 10:
            self.logger.warn(
                f"There are {len(all_skill_codes)} to be added, it's problematic!! skipping...")
            all_skill_codes = random.sample(all_skill_codes, 10)

        # self.skill_manager.conclude_skills(context, info, all_skill_codes)
        for marker, full_code in all_skill_codes:
            code = f'''theory Scratch\n  imports Complex_Main\nbegin\n\n{full_code}\nend'''
            result, *_ = self.env.step(code, quick_check=True)
            if result is True:
                self.skill_manager.add_new_skill(
                    skill_name=self.env.get_lemma_name(marker),
                    description="",
                    marker=marker,
                    full_code=full_code,
                    origin=f"{task}_v{self.curriculum_agent.get_task_retry_count(task)}",
                    init_update_count=-1,
                )

        return messages, reward, done, info

    def learn(self, reset_env=True):
        while True:
            task, context = self.curriculum_agent.propose_next_task(
                max_retries=5)
            if task is None:
                break

            task_retried_cnt = self.curriculum_agent.get_task_retry_count(task)
            self.logger.info(
                f"Starting task {task} at {task_retried_cnt + 1} try and for at most {self.action_agent_task_max_retries} error correction"
            )
            try:
                messages, reward, done, info = self.rollout(
                    task=task,
                    context=context,
                    reset_env=reset_env,
                )
            except TabError as e:
                info = {
                    "task": task,
                    "success": False,
                }
                # reset isabelle
                self.env.reset(hard_reset=True)
                time.sleep(3)  # wait for prior programme to init
                # use red color background to print the error
                self.logger.info(
                    "Your last round rollout terminated due to error:")
                self.logger.info(f"\033[41m{e}")

            self.curriculum_agent.update_exploration_progress(info)
            self.logger.info(
                f"Completed tasks: {', '.join(self.curriculum_agent.completed_tasks)}"
            )
            self.logger.info(
                f"Failed tasks: {', '.join(self.curriculum_agent.failed_tasks)}"
            )

            n_complete_task = len(set(list(filter(
                lambda x: "data/full_data" in x, self.curriculum_agent.completed_tasks))))
            n_failed_task = len(set(list(filter(
                lambda x: "data/full_data" in x, self.curriculum_agent.failed_tasks))))

            self.logger.info(f"Number of completed tasks: {n_complete_task}")
            self.logger.info(f"Number of failed tasks: {n_failed_task}")
            self.logger.info(
                f"pass rate: {n_complete_task / (n_complete_task + n_failed_task)}")

            print(f"Success: {info['success']} - [{task}], try: {task_retried_cnt + 1},",
                  f"Progress: {n_complete_task + n_failed_task}/244,",
                  f"Sketch remaining: {self.curriculum_agent.miniF2F_tasks.qsize()}"
                  f"Pass rate: {n_complete_task / (n_complete_task + n_failed_task)}", flush=True)
            os.makedirs(f"{self.ckpt_dir}/json_logs", exist_ok=True)
            U.dump_json(
                info, f"{self.ckpt_dir}/json_logs/task_{context['problem_name']}_try{task_retried_cnt + 1}.json")

        return {
            "completed_tasks": self.curriculum_agent.completed_tasks,
            "failed_tasks": self.curriculum_agent.failed_tasks,
            "skills": self.skill_manager.skills,
        }
