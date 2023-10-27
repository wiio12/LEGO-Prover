number_of_processes = input("Enter the number of processes you want to run at the same time:\n").strip()
number_of_processes = int(number_of_processes)
import glob
import os
script = 'echo "y" | sbt "runMain pisa.server.ConjecturerParser {} {} {} {}"'

total_cmds = list()
total_files = 0
for file_name in glob.glob("/home/ywu/afp-2021-02-11/thys/**/*.thy", recursive=True):
    project_single_name = file_name.split("/")[5]
    if not os.path.isdir(os.path.join("conjecturer_extractions", project_single_name)):
        os.makedirs(os.path.join("conjecturer_extractions", project_single_name))

    theory_single_name = file_name.split("/")[-1].split(".thy")[0]
    if os.path.isfile(os.path.join("conjecturer_extractions", project_single_name, theory_single_name+".src")):
        continue
    thys_index = file_name.split("/").index("thys")
    working_directory = "/".join(file_name.split("/")[:thys_index+2])
    total_cmds.append(script.format(file_name,
                                    working_directory,
                                    "/home/ywu/Isabelle2020",
                                    "conjecturer_extractions/"+project_single_name
                                    ))
    total_files += 1

process_number_to_cmds = {i: [] for i in range(number_of_processes)}
print("A total of {} files are due to be generated".format(total_files))
for i, cmd in enumerate(total_cmds):
    process_number_to_cmds[i%number_of_processes].append(cmd)

for process_number, process_cmds in process_number_to_cmds.items():
    with open("conjecturer_parser_{}.sh".format(process_number), "w") as f:
        for process_cmd in process_cmds:
            f.write(process_cmd+"\n")
            f.write("PIDmain=$!\n")
            f.write("wait $PIDmain\n")