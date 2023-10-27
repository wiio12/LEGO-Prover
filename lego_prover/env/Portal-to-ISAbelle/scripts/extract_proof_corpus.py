import os
import sys
from tqdm import tqdm

file_path = sys.argv[1]
tgt_file_path = file_path.replace("src", "tgt")
output_file_path = sys.argv[2]

valid_proofs = list()

lines = open(file_path).readlines()
tgt_lines = open(tgt_file_path).readlines()

theorem_declaration = lines[0].strip()
for i, line in tqdm(enumerate(lines)):
    line = line.strip()
    if theorem_declaration in line:
        pass
    else:
        theorem_declaration = line
        valid_proofs.append(lines[i-1].strip() + " \\n " + tgt_lines[i-1].strip())

with open(output_file_path, "w") as fout:
    for proof in valid_proofs:
        fout.write(proof)
        fout.write("\n")