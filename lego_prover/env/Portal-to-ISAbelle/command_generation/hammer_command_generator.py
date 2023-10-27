number_of_processes = input("Enter the number of processes you want to run at the same time:\n").strip()
number_of_processes = int(number_of_processes)
mini = input("Are we doing MiniF2F? (Y/N)\n").strip()
mini = True if mini.strip().startswith("Y") else False
heuristic = input("Are we doing heuristics? (Y/N)\n").strip()
heuristic = True if heuristic.strip().startswith("Y") else False
import glob
import os

if heuristic:
    script = 'echo "y" | sbt "runMain pisa.agent.PisaHammerTest {} true"'
else:
    script = 'echo "y" | sbt "runMain pisa.agent.PisaHammerTest {} false"'

theorem_names_path = "/home/qj213/mini_names" if mini else "/home/qj213/Portal-to-ISAbelle/universal_test_theorems"

total_cmds = list()
total_files = 0
for file_name in glob.glob(f"{theorem_names_path}/test_name_*.json", recursive=True):
    number = int(file_name.split("/")[-1].rstrip(".json").split("_")[-1])
    if number <= 1000:
        total_cmds.append(script.format(file_name))
        total_files += 1

process_number_to_cmds = {i: [] for i in range(number_of_processes)}
print("A total of {} files are due to be generated".format(total_files))
for i, cmd in enumerate(total_cmds):
    process_number_to_cmds[i%number_of_processes].append(cmd)

for process_number, process_cmds in process_number_to_cmds.items():
    with open("scripts/eval_hammer_{}.sh".format(process_number), "w") as f:
        for process_cmd in process_cmds:
            f.write(process_cmd+"\n")
            f.write("PIDmain=$!\n")
            f.write("wait $PIDmain\n")
            # f.write("ps -ef | grep z3 | awk '{print $2}' | xargs kill -9\n")
            # f.write("ps -ef | grep veriT | awk '{print $2}' | xargs kill -9\n")
            # f.write("ps -ef | grep cvc4 | awk '{print $2}' | xargs kill -9\n")
            # f.write("ps -ef | grep eprover | awk '{print $2}' | xargs kill -9\n")
            # f.write("ps -ef | grep SPASS | awk '{print $2}' | xargs kill -9\n")
