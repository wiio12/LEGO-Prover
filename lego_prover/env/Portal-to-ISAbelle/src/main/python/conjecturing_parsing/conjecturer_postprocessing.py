import os
import json
import glob
from tqdm import tqdm
import random

def process_string(input_string):
    return " ".join(input_string.replace("\n", " ").split())

problem_names_split = json.load(open("data/fs_with_state/problem_names_split.json"))

train_names = problem_names_split['train']
val_names = problem_names_split['val']
test_names = problem_names_split['test']

train_theorem_names = {process_string(element[1]): element[0] for element in train_names}
val_theorem_names = {process_string(element[1]): element[0] for element in val_names}
test_theorem_names = {process_string(element[1]): element[0] for element in test_names}

total_theorems = {"train": set(), "val": set(), "test": set()}
for file_name in tqdm(glob.glob("data/conjecturer_extractions/**/*.src")):
    tgt_file_name = file_name.replace("src", "tgt")
    tgt_lines = open(tgt_file_name).readlines()

    for i, line in enumerate(open(file_name).readlines()):
        theorem_name = line.split("Proof:")[1].split("State:")[0].split("\\n")[0].strip()

        if theorem_name in test_theorem_names:
            save_file = os.path.join("data/conjecturer_seq2seq", "test.src")
            total_theorems["test"].add(theorem_name)
        elif theorem_name in val_theorem_names:
            save_file = os.path.join("data/conjecturer_seq2seq", "val.src")
            total_theorems["val"].add(theorem_name)
        elif theorem_name in train_theorem_names:
            save_file = os.path.join("data/conjecturer_seq2seq", "train.src")
            total_theorems["train"].add(theorem_name)
        else:
            save_file = False
        if save_file:
            with open(save_file, "a") as fhand:
                fhand.write(line)
            with open(save_file.replace("src", "tgt"), "a") as f_tgt_hand:
                f_tgt_hand.write(tgt_lines[i])

print("Total possible train theorems: {}".format(len(train_theorem_names)))
print("Conjecturing train theorems: {}".format(len(total_theorems["train"])))
print("Total possible test theorems: {}".format(len(test_theorem_names)))
print("Conjecturing test theorems: {}".format(len(total_theorems["test"])))

parsed_test_names = list(total_theorems["test"])
random.shuffle(parsed_test_names)
for i in range(3000):
    json_to_save = [
        [test_theorem_names[parsed_test_names[i]], parsed_test_names[i]]
    ]
    json.dump(json_to_save, open("universal_test_theorems/test_name_{}.json".format(i), "w"))

    if i < 300:
        json.dump(json_to_save, open("universal_test_theorems/quick_test_name_{}.json".format(i), "w"))
