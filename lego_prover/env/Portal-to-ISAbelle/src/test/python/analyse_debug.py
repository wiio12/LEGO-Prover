import os
import sys

state_only_total_ground_truth_length = 0
proof_and_state_total_ground_truth_length = 0
state_only_proved = 0
state_only_matched = 0
proof_state_proved = 0
proof_state_matched = 0

total_one_liners = 0
for file_name in os.listdir("debug"):
    if file_name.startswith("debug"):
        file_content = open(os.path.join("debug", file_name)).readlines()
        ground_truth_length = int(file_content[0].strip("\n").split(" ")[-2])
        if ground_truth_length == 1:
            total_one_liners += 1
            if file_content[1].strip("\n").split(" ")[-2].startswith("t"):
                state_only_proved += 1
                state_only_matched += int(file_content[2].strip("\n").split(" ")[-2])
                state_only_total_ground_truth_length += ground_truth_length
            if file_content[3].strip("\n").split(" ")[-2].startswith("t"):
                proof_state_proved += 1
                proof_state_matched += int(file_content[4].strip("\n").split(" ")[-2])
                proof_and_state_total_ground_truth_length += ground_truth_length

print("State only proved: {}".format(state_only_proved))
print("State only matched: {}".format(state_only_matched))
print("State only ground truth length: {}".format(state_only_total_ground_truth_length))
print("Proof and state proved: {}".format(proof_state_proved))
print("Proof and state matched: {}".format(proof_state_matched))
print("Proof and state ground truth length: {}".format(proof_and_state_total_ground_truth_length))
print("Total one liners: {}".format(total_one_liners))