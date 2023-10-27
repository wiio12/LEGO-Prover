from __future__ import print_function

import os
import json
import grpc

from copy import copy
from func_timeout import func_set_timeout

import server_pb2
import server_pb2_grpc

MAX_MESSAGE_LENGTH = 10485760


def create_stub(port=9000):
    channel = grpc.insecure_channel('localhost:{}'.format(port),
                                    options=[('grpc.max_send_message_length', MAX_MESSAGE_LENGTH),
                                             ('grpc.max_receive_message_length', MAX_MESSAGE_LENGTH)])
    return server_pb2_grpc.ServerStub(channel)


class IsaFlexEnv:
    def __init__(self, port=9000, isa_path="/Applications/Isabelle2020.app/Isabelle",
                 starter_string="theory Test imports Complex_Main begin",
                 working_directory="/Users/qj213/Projects/afp-2021-02-11/thys/Functional-Automata"):
        self.port = port
        self.isa_path = isa_path
        self.starter_string = starter_string
        self.working_directory = working_directory

        self.stub = None
        self.obs_string = None
        self.successful_starting = False
        self.reset()

    def observation(self):
        return self.obs_string
        
    def is_finished(self, name_of_tls):
        returned_string = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=f"<is finished> {name_of_tls}")).state.strip()
        if returned_string.startswith("t"):
            return True
        else:
            return False

    @staticmethod
    def reward(done):
        return 1. if done else 0.

    def reset(self):
        self.stub = create_stub(port=self.port)
        try:
            print(self.stub.InitialiseIsabelle(server_pb2.IsaPath(path=self.isa_path)).message)
            print(self.stub.IsabelleWorkingDirectory(server_pb2.IsaPath(path=self.working_directory)).message)
            print(self.stub.IsabelleContext(server_pb2.IsaContext(context=self.starter_string)).message)
            self.successful_starting = True
        except Exception as e:
            print("Failure at initialising Isabelle process. "
                  "Make sure the path your provide is where the Isabelle executable is.")
            print(e)
        return self.obs_string

    @func_set_timeout(1800, allowOverride=True)
    def step_to_top_level_state(self, action, tls_name, new_name):
        # last_obs_string = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=f"<get state> {tls_name}")).state
        obs_string = "Step error"
        done = False
        try:
            obs_string = self.stub.IsabelleCommand(
                server_pb2.IsaCommand(command=f"<apply to top level state> {tls_name} <apply to top level state> {action} <apply to top level state> {new_name}")).state
        except Exception as e:
            print("***Something went wrong***")
            print(e)

        done = self.is_finished(new_name)
        # done = True if ("subgoal" in last_obs_string and "subgoal" not in obs_string) else False
        return obs_string, self.reward(done), done, {}

    def proceed_after(self, line_string):
        return self.post(f"<proceed after> {line_string}", forceTimeout=10000)

    def clone_to_new_name(self, new_name):
        return self.post(f"<clone> default <clone> {new_name}", forceTimeout=10)

    @func_set_timeout(1800, allowOverride=True)
    def post(self, action):
        return self.stub.IsabelleCommand(server_pb2.IsaCommand(command=action)).state
        # last_obs_string = self.obs_string
        # try:
        #     self.obs_string = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=action)).state
        # except Exception as e:
        #     print("***Something went wrong***")
        #     print(e)

        # # done = self.is_finished(self.obs_string)
        # done = self.is_finished("default")

        # return self.obs_string, self.reward(done), done, {}

    # def human_play(self):
    #     done = False
    #     while not done:
    #         print(self.obs_string)
    #         human_proof_line = input("Your tactic is my command: ")
    #         if human_proof_line == "exit":
    #             break
    #         else:
    #             obs, _, done, _ = self.step(human_proof_line)
    #             print(obs)
    #             print("=" * 50)

    # def clone_top_level_state(self, tls_name):
    #     try:
    #         message = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=f"<clone> {tls_name}")).state
    #         print(message)
    #         print(f"Cloned state called {tls_name}")
    #     except Exception as e:
    #         print("**Clone unsuccessful**")
    #         print(e)

    def proceed_to_line(self, line_stirng, before_after):
        assert before_after in ["before", "after"]
        try:
            command = f"<proceed {before_after}> {line_stirng}"
            print(command)
            message = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=command)).state
            print(message)
        except Exception as e:
            print("Failure to proceed before line")
            print(e)


def parsed_json_to_env_and_dict(path_to_json, afp_path, port=9000, isa_path="/Applications/Isabelle2020.app/Isabelle"):
    save_dict = json.load(open(path_to_json))
    project = save_dict["project"]
    wd = os.path.join(afp_path, "thys", project)
    segments = save_dict["segments"]
    # Find starter string
    starter_string = None
    for line in segments:
        if line.strip().startswith("theory"):
            starter_string = " ".join(line.strip().split("\n"))
            break
    assert starter_string
    # print(port, isa_path, starter_string, wd, segments)
    return IsaFlexEnv(port=port, isa_path=isa_path,
                     starter_string=starter_string,
                     working_directory=wd), save_dict


def initialise_env(port, isa_path, theory_file_path=None, working_directory=None):
    return IsaFlexEnv(port=port, isa_path=isa_path, starter_string=theory_file_path, working_directory=working_directory)


def initialise_problem(env, problem_name):
    env.proceed_to_line(problem_name, "after")
    return env


if __name__ == '__main__':
    env = initialise_env(8000, 
        working_directory="/Applications/Isabelle2021.app/src/HOL/Examples",
        isa_path="/Applications/Isabelle2021.app", 
        theory_file_path="/Applications/Isabelle2021.app/src/HOL/Examples/Adhoc_Overloading_Examples.thy"
    )
    print(env.post("<get_ancestors>"))
