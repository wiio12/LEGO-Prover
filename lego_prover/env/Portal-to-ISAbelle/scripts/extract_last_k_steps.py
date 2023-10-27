import argparse
import os
from tqdm import tqdm


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Extract the last k steps of the proof to be used in automated proof search.")
    parser.add_argument("--path-to-proof-and-state-file", "-ptpasf", type=str, help="Path to the file of the proof steps and states.")
    parser.add_argument("--k", type=int, help="The number of steps you want to extract.")
    parser.add_argument("--dump-path", "-dp", type=str, help="Path to dump the resulting files.")
    args = parser.parse_args()

    file_name = args.path_to_proof_and_state_file.split("/")[-1]
    k_step = args.k

    with open(os.path.join(args.dump_path, f"last_{k_step}_step_{file_name}"), "w") as f_out, \
            open(args.path_to_proof_and_state_file) as f_in:
        for line in tqdm(f_in.readlines()):
            line = line.strip()
            proof = line.split("<PS_SEP>")[0].strip().lstrip("Proof: ")
            state = line.split("State:")[1].strip()
            
            proof_steps = proof.split("\\n")
            last_k_proof_steps = [element.strip() for element in proof_steps[-k_step:]]
            last_k_proof_steps_string = " \\n ".join(last_k_proof_steps)
            new_line = f"Proof: {last_k_proof_steps_string} State: {state}"
            f_out.write(new_line)
            f_out.write("\n")
