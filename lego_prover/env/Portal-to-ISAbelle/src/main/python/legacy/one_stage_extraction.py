import os
import json
import grpc
import argparse

from copy import copy
from func_timeout import func_set_timeout, FunctionTimedOut

import server_pb2
import server_pb2_grpc


MAX_MESSAGE_LENGTH = 10485760


def analyse_whole_file(whole_file_string, use_sledgehammer=False):
    transitions = whole_file_string.split("<\TRANSEP>")
    state_action_proof_level_tuples = list()
    problem_names = list()
    proof_open = False
    last_state = ""
    for transition in transitions:
        if not transition:
            continue
        if use_sledgehammer:
            state, action, proof_level, hammer_results = transition.split("<\STATESEP>")
        else:
            state, action, proof_level = transition.split("<\STATESEP>")
            hammer_results = "NA"
        state = state.strip()
        action = action.strip()
        proof_level = int(proof_level.strip())
        if action.startswith("lemma") or action.startswith("theorem"):
            problem_names.append(action)
            state_action_proof_level_tuples.append((state, action, proof_level, hammer_results))
            proof_open = True
        elif proof_open:
            state_action_proof_level_tuples.append((state, action, proof_level, hammer_results))

        if "subgoal" in last_state and "subgoal" not in state:
            proof_open = False
    return {
        "problem_names": problem_names,
        "translations": state_action_proof_level_tuples
    }


@func_set_timeout(12000)
def isa_step(stub, theory_file_path, use_sledgehammer=False):
    stub.IsabelleContext(server_pb2.IsaContext(context=theory_file_path))
    extraction_command = "PISA extract data with hammer" if use_sledgehammer else "PISA extract data"
    return stub.IsabelleCommand(server_pb2.IsaCommand(command=extraction_command)).state


def extract_file(isa_path, theory_file_path, working_directory, saving_directory, port=9000, use_sledgehammer=False):
    channel = grpc.insecure_channel('localhost:{}'.format(port),
                                    options=[('grpc.max_send_message_length', MAX_MESSAGE_LENGTH),
                                    ('grpc.max_receive_message_length', MAX_MESSAGE_LENGTH)])
    stub = server_pb2_grpc.ServerStub(channel)

    stub.InitialiseIsabelle(server_pb2.IsaPath(path=isa_path))
    stub.IsabelleWorkingDirectory(server_pb2.IsaPath(path=working_directory))

    if not os.path.isdir(saving_directory):
        os.makedirs(saving_directory)
    close_program = False
    try:
        whole_file_parsed = isa_step(stub, theory_file_path, use_sledgehammer=use_sledgehammer)
        stub.IsabelleCommand(server_pb2.IsaCommand(command="exit"))
    except (Exception, FunctionTimedOut) as e:
        close_program = True
        with open(os.path.join(saving_directory,
                               "project_{}_file_{}_bug_report.txt".format(
                                   working_directory.split("/")[-1], theory_file_path.split("/")[-1])), "w") as fout:
            fout.write(str(e))

    file_analysis = analyse_whole_file(whole_file_parsed)
    file_info = {
        "file_name": theory_file_path,
        "working_directory": working_directory,
        **file_analysis,
        "raw_parsed_string": whole_file_parsed
    }
    
    json.dump(file_info,
              open(os.path.join(saving_directory,
                                "_".join(theory_file_path.split(".thy")[0].split("/"))+"_ground_truth.json"), "w"))

    if close_program:
        stub.IsabelleCommand(server_pb2.IsaCommand(command="exit"))
    channel.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Extracting an Isabelle theory file.')
    parser.add_argument('--isa-path', help='The path to the Isabelle executable',
                        default="/Applications/Isabelle2020.app/Isabelle")
    parser.add_argument('--working-directory', '-wd', help='Path to the AFP project')
    parser.add_argument('--theory-file-path', '-tfp', help='Path to the file to parse')
    parser.add_argument('--saving-directory', '-sd', help='Where the save the parsed json files')
    parser.add_argument('--port', '-p', help='Port to use to communicate', default=9000, type=int)
    parser.add_argument('--use-sledgehammer', '-us', help='Whether to use sledgehammer',
                        action='store_true')
    parser.set_defaults(use_sledgehammer=False)
    args = parser.parse_args()

    # for file_name in os.listdir(args.working_directory):
    #     if file_name.endswith(".thy"):
    #         full_file_path = os.path.join(args.working_directory, file_name)
    extract_file(args.isa_path, args.theory_file_path, args.working_directory,
                 args.saving_directory, args.port, args.use_sledgehammer)
