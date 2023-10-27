import os
import json
import grpc
import argparse

import server_pb2
import server_pb2_grpc

MAX_MESSAGE_LENGTH = 10485760


def stack_lines(input_string):
    return " ".join(input_string.replace("\n", " ").split()).strip()


def evaluate_single_problem(isa_path, theory_file_path, working_directory, theorem_name, model, mode_of_proving,
                       maximum_number_of_steps=100, port=9000):
    channel = grpc.insecure_channel('localhost:{}'.format(port),
                                    options=[('grpc.max_send_message_length', MAX_MESSAGE_LENGTH),
                                             ('grpc.max_receive_message_length', MAX_MESSAGE_LENGTH)])
    stub = server_pb2_grpc.ServerStub(channel)
    stub.InitialiseIsabelle(server_pb2.IsaPath(path=isa_path))
    stub.IsabelleWorkingDirectory(server_pb2.IsaPath(path=working_directory))
    stub.IsabelleContext(server_pb2.IsaContext(context=theory_file_path))

    theorem_name = stack_lines(theorem_name)
    state_string = stub.IsabelleCommand(server_pb2.IsaCommand(command="proceed:"+theorem_name)).state

    if mode_of_proving not in ["proof", "state", "proof_and_state"]:
        raise AssertionError

    previous_proof_segment = theorem_name
    state = state_string
    # print(state)
    try:
        for i in range(maximum_number_of_steps):
            state = stack_lines(state)
            input_string = ""
            if mode_of_proving == "state":
                input_string += "State: {}".format(state)
            if mode_of_proving == "proof_and_state":
                input_string += " <PS_SEP> "
            if mode_of_proving == "proof":
                input_string += "Proof: {}".format(previous_proof_segment)
                # TODO: previous proof segment unfinished

            output_string = model.predict(input_string)
            # print(input_string)
            # print(output_string)
            state = stub.IsabelleCommand(server_pb2.IsaCommand(command=output_string)).state
            # print(state)
            if "proof" not in state:
                stub.IsabelleCommand(server_pb2.IsaCommand(command="exit"))
                return 1
    except Exception as e:
        print(e)
        pass
    stub.IsabelleCommand(server_pb2.IsaCommand(command="exit"))
    return 0


class DummyProver:
    def __init__(self, seq2seq_repo):
        src_list = open(os.path.join(seq2seq_repo, "train.src"), "r").readlines()
        tgt_list = open(os.path.join(seq2seq_repo, "train.tgt"), "r").readlines()
        src_list.extend(open(os.path.join(seq2seq_repo, "val.src"), "r").readlines())
        tgt_list.extend(open(os.path.join(seq2seq_repo, "val.tgt"), "r").readlines())
        src_list.extend(open(os.path.join(seq2seq_repo, "test.src"), "r").readlines())
        tgt_list.extend(open(os.path.join(seq2seq_repo, "test.tgt"), "r").readlines())
        self.prover_dict = dict()
        assert len(src_list) == len(tgt_list)
        for i in range(len(src_list)):
            src = stack_lines(src_list[i])
            tgt = stack_lines(tgt_list[i])
            self.prover_dict[src] = tgt

    def predict(self, input_string):
        return self.prover_dict[input_string]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Extracting an Isabelle theory file.')
    parser.add_argument('--isa-path', help='The path to the Isabelle executable',
                        default="/Applications/Isabelle2020.app/Isabelle")
    parser.add_argument('--working-directory', '-wd', help='Path to the AFP project')
    parser.add_argument('--theory-file-path', '-tfp', help='Path to the file to parse')
    parser.add_argument('--theorem-name', '-tn', help='Name of the theorem to prove')
    parser.add_argument('--mode-of-proving', '-mop',
                        help='Mode of proving, could be "state", "proof", or "proof_and_state"')
    parser.add_argument('--port', '-p', help='Port to use to communicate', default=9000, type=int)
    args = parser.parse_args()

    dummy_prover = DummyProver("/Users/qj213/Projects/PISA/fs_with_state")
    # print(evaluate_single_problem(isa_path=args.isa_path, theory_file_path=args.theory_file_path,
    #                          working_directory=args.working_directory, theorem_name=args.theorem_name,
    #                          port=args.port, model=dummy_prover, mode_of_proving="state"))

    problem_names = json.load(open("fs_with_state/problem_names_split.json"))
    train_names = problem_names["train"]
    for i in range(0, 5):
        theory_file_path = train_names[i][0].replace("/home/ywu/afp-2021-02-11", "/Users/qj213/Projects/afp-2021-02-11")
        # print(theory_file_path)
        # print(train_names[i][1])
        print(evaluate_single_problem(isa_path=args.isa_path,
                               theory_file_path=theory_file_path,
                               working_directory="/".join(theory_file_path.split("/")[:-1]),
                               theorem_name=train_names[i][1],
                               port=args.port, model=dummy_prover, mode_of_proving="state"))