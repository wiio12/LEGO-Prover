import json
import os
import sys


path_to_dir = "data/seq2seq/seq2seq_with_proof_and_state"

ground_truth_dictionary = {}
with open(os.path.join(path_to_dir, "test.src")) as f1, open(os.path.join(path_to_dir, "test.tgt")) as f2:
    src_lines = list(f1.readlines())
    tgt_lines = list(f2.readlines())
    for i in range(len(src_lines)):
        src = src_lines[i].rstrip("\n")
        tgt = tgt_lines[i].rstrip("\n")
        ground_truth_dictionary[src] = i

good_ones = set()
for file_name in os.listdir("universal_test_theorems"):
    problem_index = int(file_name.split("_")[-1].split(".")[0])
    if file_name.startswith("quick"):
        file_content = json.load(open(os.path.join("universal_test_theorems", file_name)))
        theorem_declaration = file_content[0][1]
        for key in ground_truth_dictionary:
            if theorem_declaration in key:
                good_ones.add((problem_index, ground_truth_dictionary[key]))

with open("debug/good_indices.txt", "w") as fout:
    for good_index in good_ones:
        # Problem index, line index
        fout.write("{} | {}".format(good_index[0], good_index[1]))
        fout.write("\n")
