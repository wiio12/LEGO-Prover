import sys
import os
target_directory = sys.argv[1]

test_sentences = []
with open("data/seq2seq/seq2seq_with_state/test.tgt") as fhand:
    for line in fhand.readlines():
        test_sentences.append(line.strip().rstrip("\n"))
test_sentences = set(test_sentences)

succ_proofs = 0
originality = 0
for file_name in os.listdir(target_directory):
    if file_name.startswith("succ"):
        succ_proofs += 1
        with open(os.path.join(target_directory, file_name)) as fhand:
            ground_truth_lines = 0
            total_lines = fhand.readlines()
            for line in total_lines:
                line = line.strip().rstrip("\n")
                if line in test_sentences:
                    ground_truth_lines += 1
            originality += ground_truth_lines / len(total_lines)
print("Originality: {}".format(1-originality/succ_proofs))