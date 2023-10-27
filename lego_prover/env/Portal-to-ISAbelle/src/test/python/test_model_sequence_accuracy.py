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

final_line = " PROOFSTEP\", \"best_of\": 1, \"temperature\": 0, \"max_tokens\": 128, \"n\": 1}'"
if state_only:
    path_to_dir = "pisa_seq2seq/state_only"
    preceding_line = """curl https://api.openai.com/v1/engines/formal-small-isabelle-v6-c4/completions -H 'Content-Type: application/json' -H 'Authorization: Bearer <OPENAI_TOKEN>' -d '{\"prompt\": \""""

else:
    path_to_dir = "pisa_seq2seq/proof_and_state"
    preceding_line = """curl https://api.openai.com/v1/engines/formal-small-isabelle-wproof-v1-c4/completions -H 'Content-Type: application/json' -H 'Authorization: Bearer <OPENAI_TOKEN>' -d '{\"prompt\": \""""

ground_truth_dictionary = {}

with open(os.path.join(path_to_dir, "val.src")) as f1, open(os.path.join(path_to_dir, "val.tgt")) as f2:
    src_lines = list(f1.readlines())
    tgt_lines = list(f2.readlines())
    for i in range(len(src_lines)):
        src = src_lines[i].rstrip("\n")
        tgt = tgt_lines[i].rstrip("\n")
        ground_truth_dictionary[src] = tgt
        # print(src)
        # print(tgt)
        # break


def preprocess(cmd, state_only):
    if state_only:
        returned_cmd = cmd.replace("State:", "[IS] GOAL").replace("\\", "\\\\").replace("\n", "\\n")\
            .replace("\"", "\\\"").replace("\'", "\\u0027")
    else:
        returned_cmd = cmd.replace("Proof:", "[IS] PROOF").replace("State:", "[IS] GOAL").replace("\\", "\\\\")\
            .replace("\n", "\\n") \
            .replace("\"", "\\\"").replace("\'", "\\u0027")
    return returned_cmd


random_keys = list(ground_truth_dictionary.keys())
random.shuffle(random_keys)
correct = 0
for src_line in tqdm(random_keys[:1000]):
    cmd = preprocess(src_line, state_only)
    cmd = preceding_line + cmd + final_line
    # print(cmd)
    stream = os.popen(cmd)
    output = stream.read().rstrip("\n")
    try:
        text = json.loads(output)["choices"][0]["text"].strip()
        # print(text)
        # print(text)
        # print(ground_truth_dictionary[src_line])
        # print(text == ground_truth_dictionary[src_line])
        if text == ground_truth_dictionary[src_line]:
            correct += 1
    except Exception as e:
        print(e)

print(correct/1000)
