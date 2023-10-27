import glob
import os
import shutil

number_of_processes = input("Enter the number of processes you want to run at the same time:\n").strip()
number_of_processes = int(number_of_processes)

script = 'echo "y" | sbt "test:runMain pisa.TransparentComparison {}"'

total_cmds = list()
pattern = "/home/ywu/PISA/universal_test_theorems/quick_test_name_*.json"

for file_name in glob.glob(pattern, recursive=True):
    total_cmds.append(script.format(file_name))

process_number_to_cmds = {i: [] for i in range(number_of_processes)}
for i, cmd in enumerate(total_cmds):
    process_number_to_cmds[i%number_of_processes].append(cmd)

for process_number, process_cmds in process_number_to_cmds.items():
    with open("scripts/test_search_{}.sh".format(process_number), "w") as f:
        for process_cmd in process_cmds:
            f.write(process_cmd+"\n")
            f.write("PIDmain=$!\n")
            f.write("wait $PIDmain\n")