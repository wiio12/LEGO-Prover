import os

proof_dict = {}
for file_name in os.listdir("results/hammer_eval"):
    if file_name.endswith("out"):
        theorem_number = file_name.split("_")[0]
        info_file_name = file_name.replace("out", "info")
        info_file_path = os.path.join("results/hammer_eval", info_file_name)
        if os.path.isfile(info_file_path):
            info_lines = open(info_file_path).readlines()
            proved = open(os.path.join("results/hammer_eval", file_name)).read().strip()
            proved = True if (proved.startswith("t") or proved.startswith("T")) else False
            proof_dict[theorem_number] = (proved, info_lines)

with open("results/hammer_eval/success", "w") as fhand:
    for theorem_number in proof_dict:
        info_tuple = proof_dict[theorem_number]
        if info_tuple[0]:
            fhand.writelines(info_tuple[1])
            fhand.write("\n\n")

with open("results/hammer_eval/failure", "w") as fhand:
    for theorem_number in proof_dict:
        info_tuple = proof_dict[theorem_number]
        if not info_tuple[0]:
            fhand.writelines(info_tuple[1])
            fhand.write("\n\n")