import os
import json

from tqdm import tqdm

proof_and_state_dir = "/home/qj213/proof_and_state"
first_step_dir = "/home/qj213/first_step"


for file in os.listdir(proof_and_state_dir):
    split_name = file.split(".")[0]
    with open(os.path.join(proof_and_state_dir, file)) as fhand, \
        open(os.path.join(first_step_dir, f"{split_name}.src"), "w") as src_out, \
            open(os.path.join(first_step_dir, f"{split_name}.tgt"), "w") as tgt_out:
        for line in tqdm(fhand.readlines()):
            line_json = json.loads(line.strip())
            source = line_json["source"]
            proof_step_string = source.split("<PS_SEP>")[0].strip()
            proof_state_string = source.split("<PS_SEP>")[1].strip()
            target = line_json["target"]
            if "\\n" not in proof_step_string:
                # This is the first step
                src_out.write(f"<ISA_OBS> {proof_state_string}\n")
                tgt_out.write(f"{target}\n")

