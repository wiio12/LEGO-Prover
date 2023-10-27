import os
import sys
import json
import random
from tqdm import tqdm


random.seed(0)

if sys.argv[1] == "state":
    state_only = True
elif sys.argv[1] == "proof_state":
    state_only = False
else:
    raise NotImplementedError

if state_only:
    path_to_dir = "data/seq2seq/seq2seq_with_state"
    output_dir = "debug/with_state"
else:
    path_to_dir = "data/seq2seq/seq2seq_with_proof_and_state"
    output_dir = "debug/with_proof_and_state"

line_index_to_pair = dict()
with open(os.path.join(path_to_dir, "test.src")) as f1, open(os.path.join(path_to_dir, "test.tgt")) as f2:
    src_lines = list(f1.readlines())
    tgt_lines = list(f2.readlines())
    for i in range(len(src_lines)):
        src = src_lines[i].rstrip("\n")
        tgt = tgt_lines[i].rstrip("\n")
        line_index_to_pair[i] = (src, tgt)

problem_index_to_line_indices = dict()
with open("debug/good_indices.txt") as fin:
    for line in fin.readlines():
        line = line.rstrip("\n")
        problem_index, line_index = line.split("|")
        problem_index = int(problem_index.strip())
        line_index = int(line_index.strip())

        if problem_index not in problem_index_to_line_indices:
            problem_index_to_line_indices[problem_index] = [line_index]
        else:
            problem_index_to_line_indices[problem_index].append(line_index)

for problem_index in range(300):
    line_indices = problem_index_to_line_indices[problem_index]
    line_indices = sorted(line_indices)
    with open(os.path.join(output_dir, "{}_pairs.txt".format(problem_index)), "w") as fout:
        for line_index in line_indices:
            pair = line_index_to_pair[line_index]
            fout.write("{} <SEP> {}".format(pair[0], pair[1]))
            fout.write("\n")
