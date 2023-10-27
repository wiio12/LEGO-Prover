import json
import random
import shutil

from tqdm import tqdm
from mpmath import mp, mpf, fmod
import hashlib
import math


random.seed(0)
mp.dps = 50
DEFAULT_MAX_LENGTH = 3000


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


def extract_siblings(proof_steps, current_step_index):
    sibling_indices = []
    current_proof_level = proof_steps[current_step_index][2]
    # We shall have current_proof_level ≥ 1 since we're inside a proof
    search_index = current_step_index - 1
    while search_index >= 0:
        if proof_steps[search_index][2] > current_proof_level:
            # Unimportant proof subtree content*
            pass
        elif proof_steps[search_index][2] == current_proof_level:
            # Sibling
            sibling_indices.insert(0, search_index)
        elif proof_steps[search_index][2] < current_proof_level:
            # Higher level steps
            return sibling_indices, search_index
        search_index -= 1
    return [], None


def extract_needed(proof_steps, current_step_index, needed_found):
    if needed_found[current_step_index]:
        return needed_found[current_step_index]
    sibling_indices, search_index = extract_siblings(proof_steps, current_step_index)
    if search_index is None:
        return sibling_indices
    elif search_index > 0:
        return extract_needed(proof_steps, search_index, needed_found) + [search_index] + sibling_indices
    elif search_index == 0:
        return [search_index] + sibling_indices
    else:
        raise AssertionError


def extract_needed_string(transition, transitions_for_a_problem, previous_proof_segment, i, needed_found, kwargs):
    needed_indices = extract_needed(transitions_for_a_problem, i, needed_found)
    needed_found[i] = needed_indices
    needed_segment = " \\n ".join([transitions_for_a_problem[index][1] for index in needed_indices])
    return f"<ISA_NDS> {needed_segment} <ISA_OBS> {transition[0]}"


def extract_last_k_string(transition, transitions_for_a_problem, previous_proof_segment, i, needed_found, kwargs):
    last_k = 1 if "last_k" not in kwargs else kwargs["last_k"]
    assert isinstance(last_k, int)
    proof_lines = previous_proof_segment.strip().split(" \\n ")
    last_k_proof_lines = " \\n ".join(proof_lines[-last_k:])
    return f"<ISA_LAST_{last_k}> {last_k_proof_lines} <ISA_OBS> {transition[0]}"


def extract_proof_only_string(transition, transitions_for_a_problem, previous_proof_segment, i, needed_found, kwargs):
    return f"<ISA_PRF> {previous_proof_segment}"


def extract_state_only_string(transition, transitions_for_a_problem, previous_proof_segment, i, needed_found, kwargs):
    return f"<ISA_OBS> {transition[0]}"


def extract_proof_and_state_string(transition, transitions_for_a_problem, previous_proof_segment, i, needed_found,
                                   kwargs):
    return f"<ISA_PRF> {previous_proof_segment} <ISA_OBS> {transition[0]}"


def extract_trimmed_proof_and_state_string(transition, transitions_for_a_problem, previous_proof_segment, i,
                                           needed_found, kwargs):
    max_length = kwargs["max_length"] if "max_length" in kwargs else DEFAULT_MAX_LENGTH
    proof_lines = previous_proof_segment.strip().split(" \\n ")
    state_string = transition[0]
    proof_string = ""
    state_length = len(state_string)
    for i in reversed(range(len(proof_lines))):
        if len(proof_string) + state_length + len(proof_lines[i].strip()) > max_length:
            break
        proof_string = f"{proof_lines[i].strip()} \\n {proof_string}"

    return f"<ISA_TRIM_PRF> {proof_string} <ISA_OBS> {transition[0]}"


all_processing_methods = {
    "needed": extract_needed_string,
    "last_k": extract_last_k_string,
    "proof_only": extract_proof_only_string,
    "state_only": extract_state_only_string,
    "proof_and_state": extract_proof_and_state_string,
    "trimmed_proof_and_state": extract_trimmed_proof_and_state_string,
}


def process_translations_for_a_problem(transitions_for_a_problem, processing_method_config=None):
    """Transform the transitions for a problem to translation pairs"""
    processing_method_name, additional_args = processing_method_config

    # The first one is the lemma/theorem definition
    previous_proof_segment = transitions_for_a_problem[0][1]
    needed_found = {i: False for i in range(len(transitions_for_a_problem))}

    translation_pairs = []
    for i in range(1, len(transitions_for_a_problem)):
        transition = transitions_for_a_problem[i]
        translation_src = ""
        if processing_method_name is None or not processing_method_name in all_processing_methods:
            raise AssertionError("We must have a specified processing method")

        processing_method = all_processing_methods[processing_method_name]
        translation_src += processing_method(transition, transitions_for_a_problem, previous_proof_segment, i,
                                             needed_found, additional_args)
        translation_pairs.append((translation_src, transition[1]))
        previous_proof_segment += " \\n " + transition[1]
    return translation_pairs


def trim_string(s: str):
    """Remove all change line characters and replace them with spaces"""
    return " ".join(s.replace("\n", " ").split())


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


def process_files_with_proof_statements(file_names, saving_directory, processing_method_config=None):
    # Store everything in jsonl format, and in text src and tgt format
    datapoints = {
        "train": list(),
        "valid": list(),
        "test": list()
    }
    problem_names_split = {
        "train": list(),
        "val": list(),
        "test": list()
    }
    for file_path in tqdm(file_names, desc="Processing files"):
        file = json.load(open(file_path))
        original_file_name = file['file_name']
        problem_names = set(file['problem_names'])
        transitions_split = split_transitions(problem_names, file['translations'])

        split = None
        

        for problem_name in set(file['problem_names']):
            if "Isabelle2021/src/HOL" in original_file_name:
                split = "train" 
            else:
                split = get_split(problem_name)

            problem_names_split[split].append((original_file_name, problem_name))

            json_split = "valid" if split == "val" else split
            translation_pairs = process_translations_for_a_problem(
                transitions_split[problem_name],
                processing_method_config=processing_method_config
            )

            proof_script_till_now = [problem_name]
            for proof_state, proof_step in translation_pairs:
                sanitised_x = trim_string(proof_state)
                sanitised_y = trim_string(proof_step)
                datapoints[json_split].append(
                    {
                        "file_name": file['file_name'],
                        'problem_name': problem_name,
                        "x": sanitised_x,
                        "y": sanitised_y,
                        "proof_script_until_now": "<SEP>".join(proof_script_till_now)
                    }
                )
                proof_script_till_now.append(sanitised_y)
    
    for json_split in tqdm(datapoints.keys(), desc="Saving files"):
        # Write json
        with open(os.path.join(saving_directory, f"{json_split}.jsonl"), "w") as fout:
            for datapoint in datapoints[json_split]:
                fout.write(json.dumps(datapoint))
                fout.write("\n")

        # Write src and tgt
        split = "val" if json_split == "valid" else json_split
        with open(os.path.join(saving_directory, f"{split}.src"), "w") as f_src, \
                open(os.path.join(saving_directory, f"{split}.tgt"), "w") as f_tgt:
            for datapoint in datapoints[json_split]:
                f_src.write(datapoint["x"]+"\n")
                f_tgt.write(datapoint["y"]+"\n")
                
    json.dump(problem_names_split, open(os.path.join(saving_directory, "problem_names_split.json"), "w"))

    for split, lines in problem_names_split.items():
        split = "valid" if split == "val" else split
        
        with open(os.path.join(saving_directory, f"split.std_and_afp.{split}"), "w") as fout:
            for theory_path, theorem_name in lines:
                theorem_name = " ".join(theorem_name.strip().split())
                fout.write(f"{theory_path} <PATH_AND_THEOREM_SEP> {theorem_name}")
                fout.write("\n")


if __name__ == "__main__":
    import argparse
    import glob
    import os
    parser = argparse.ArgumentParser(description='Extracting translation pairs.')
    parser.add_argument('--extraction-file-directory', '-efd', nargs='+', help='Where the parsed json files are')
    parser.add_argument('--saving-directory', '-sd', help='Where to save the translation pairs')
    parser.add_argument('--processing-method-config', '-pmc', type=str,
                        help='Where to find the processing method config')
    parser.add_argument('--last-k', '-lk', type=int, default=1, help='How many last k steps to use')
    args = parser.parse_args()

    all_configs = {
        "needed": ("needed", {}),
        "last_k": ("last_k", {"last_k": args.last_k}),
        "proof_only": ("proof_only", {}),
        "state_only": ("state_only", {}),
        "proof_and_state": ("proof_and_state", {}),
        "trimmed_proof_and_state": ("trimmed_proof_and_state", {}),
    }
    ppc = all_configs[args.processing_method_config]
    file_suffix = args.processing_method_config

    saving_directory = "{}_with_{}".format(args.saving_directory, file_suffix)
    if os.path.isdir(saving_directory):
        shutil.rmtree(saving_directory)
    os.makedirs(saving_directory)

    file_names = []
    for extraction_file_directory in args.extraction_file_directory:
        file_names += list(glob.glob("{}/*/*_ground_truth.json".format(extraction_file_directory)))
    
    print(f"Processing {len(file_names)} files in total")
    process_files_with_proof_statements(file_names, saving_directory, ppc)
