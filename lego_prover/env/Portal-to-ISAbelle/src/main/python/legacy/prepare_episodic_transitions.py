import json
import random
import shutil
import jsonlines

from tqdm import tqdm
from mpmath import mp, mpf, fmod
import hashlib
import math


random.seed(0)
mp.dps = 50


def split_transitions(problem_names, transitions):
    transitions_for_problems = {problem_name: [] for problem_name in problem_names}
    current_problem_name = ""
    for transition in transitions:
        if transition[1] in problem_names:
            current_problem_name = transition[1]
        elif "proof" not in transition[0]:
            continue
        transitions_for_problems[current_problem_name].append(transition)
    return transitions_for_problems


def process_translations_for_a_problem(transitions_for_a_problem):
    """Transform the transitions for a problem to translation pairs"""
    # The first one is the lemma/theorem definition
    previous_proof_segment = transitions_for_a_problem[0][1]

    episodic_transitions = []
    for transition in transitions_for_a_problem[1:]:
        rl_transition = {
            "observation": transition[0],
            "extra context": previous_proof_segment,
            "action": transition[1],
            "complete": False
        }

        episodic_transitions.append(rl_transition)
        previous_proof_segment += " \\n " + transition[1]

    if episodic_transitions:
        episodic_transitions[-1]["complete"] = True
    return episodic_transitions


def trim_string(s: str):
    """Remove all change line characters and replace them with spaces"""
    return " ".join(s.replace("\n", " ").split())


def remove_extra_spaces(s: str):
    return " ".join(s.split())


def hash_string_to_int(arg):
    return int(hashlib.sha256(arg.encode("utf-8")).hexdigest(), 16) % 10**30


def hash_string_to_float(arg):
    x = mpf(hash_string_to_int(arg))
    return fmod(x * mp.pi, mpf(1.))


def get_split(arg):
    float_hash = hash_string_to_float(arg)
    if float_hash < 0.95:
        return "train"
    elif float_hash < 0.96:
        return "val"
    else:
        return "test"


def random_split_file_names(file_names, val_test_files=100):
    random.shuffle(file_names)
    return file_names[:-2 * val_test_files], file_names[-2 * val_test_files:-val_test_files], \
           file_names[-val_test_files:]


def process_files_with_proof_statements(file_names, saving_directory):
    problem_names_split = {
        "train": list(),
        "val": list(),
        "test": list()
    }
    unique_id_to_transitions = dict()
    for file_path in tqdm(file_names):
        file = json.load(open(file_path))
        original_file_name = file['file_name']
        problem_names = set(file['problem_names'])
        transitions_split = split_transitions(problem_names, file['translations'])

        for problem_name in set(file['problem_names']):
            split = get_split(problem_name)
            problem_names_split[split].append((original_file_name, problem_name))
            episodic_transitions = process_translations_for_a_problem(transitions_split[problem_name])
            unique_id_to_transitions[(original_file_name, problem_name)] = episodic_transitions

    for split, split_uids in problem_names_split.items():
        with jsonlines.open(os.path.join(saving_directory, "{}.jsonl".format(split)), "w") as writer:
            for uid in split_uids:
                writer.write(unique_id_to_transitions[uid])

    json.dump(problem_names_split, open(os.path.join(saving_directory, "problem_names_split.json"), "w"))


if __name__ == "__main__":
    import argparse
    import glob
    import os
    parser = argparse.ArgumentParser(description='Extracting translation pairs.')
    parser.add_argument('--extraction-file-directory', '-efd', help='Where the parsed json files are')
    parser.add_argument('--saving-directory', '-sd', help='Where to save the translation pairs')
    parser.add_argument('--proof', dest='proof', action='store_true')
    parser.add_argument('--state', dest='state', action='store_true')
    args = parser.parse_args()

    assert args.proof or args.state
    if args.proof and not args.state:
        proof_state_suffix = "proof"
    elif args.state and not args.proof:
        proof_state_suffix = "state"
    else:
        proof_state_suffix = "proof_and_state"

    saving_directory = args.saving_directory
    if os.path.isdir(saving_directory):
        shutil.rmtree(saving_directory)
    os.makedirs(saving_directory)

    file_names = list(glob.glob("{}/*/*_ground_truth.json".format(
        args.extraction_file_directory, proof_state_suffix)))
    process_files_with_proof_statements(file_names, saving_directory)
