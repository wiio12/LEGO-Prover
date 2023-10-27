ports = input("Enter the ports, separated by commas:\n").strip()
ports = ports.split(",")
ports = [int(port.strip()) for port in ports]
ports = [port for port in ports if port]

import glob
import os

script = "python3 src/main/python/one_stage_extraction.py -wd {} --saving-directory std_extractions/{} --isa-path /home/qj213/Isabelle2021 -tfp {}"
n_threads = 1

cmds = []

IGNORED_THEORIES = {}
IGNORED_ENTRIES = {}

total_files = 0
for project_name in glob.glob("/home/qj213/Isabelle2021/src/**/*.thy", recursive=True):
    project_single_name = project_name.split("/")[5]
    file_single_name = project_name.split("/")[-1]

    # Ignore already extracted files
    if os.path.isfile("/home/qj213/Portal-to-ISAbelle/std_extractions/{}/{}_ground_truth.json".format(
            project_single_name, file_single_name.split(".thy")[0])):
        continue

    if project_single_name not in IGNORED_ENTRIES and \
            project_single_name + "/" + file_single_name not in IGNORED_THEORIES:
        cmds.append(
            script.format("/".join(project_name.split("/")[:-1]), project_single_name, project_name))
        total_files += 1
print("A total of {} files are due to be generated".format(total_files))
# num_cmd_per_thread = len(cmds) // n_threads + 1
# cmds_splits = [cmds[i*num_cmd_per_thread:(i+1)*num_cmd_per_thread] for i in range(n_threads)]

how_many_ports = len(ports)
indices_to_ports = {i: port for i, port in enumerate(ports)}
cmds_for_port = {port: [] for port in ports}
for i, cmd in enumerate(cmds):
    port = indices_to_ports[i%how_many_ports]
    cmds_for_port[port].append(cmd + " -p {} ".format(port))

for port, port_cmds in cmds_for_port.items():
    with open("std_extract_script_{}.sh".format(port), "w") as f:
        f.write('sbt "runMain pisa.server.PisaOneStageServer{}"&\n'.format(port))
        f.write("PIDmain=$!\n")
        f.write("sleep 12\n")
        wait_cmds = []
        for i, cmd in enumerate(port_cmds):
            if (i + 1) % n_threads == 0:
                f.write(cmd + "&\n")
                f.write("PID{}=$!\n".format(i % n_threads))
                wait_cmds.append("wait $PID{}\n".format(i % n_threads))
                for wait in wait_cmds:
                    f.write(wait)
                wait_cmds = []
                # f.write("ps aux | grep scala | awk '{print $2}' | xargs kill\n")
                # f.write("ps aux | grep java | awk '{print $2}' | xargs kill\n")
                # f.write("ps aux | grep poly | awk '{print $2}' | xargs kill\n")
                f.write("kill $PIDmain\n")
                if (i+1) % 20 == 0:
                    f.write("rm -rf target/bg-jobs/* \n")
                f.write('sbt "runMain pisa.server.PisaOneStageServer{}" &\n'.format(port))
                f.write("PIDmain=$!\n")
                f.write("sleep 12\n")
            else:
                f.write(cmd + "&\n")
                f.write("PID{}=$!\n".format(i % n_threads))
                wait_cmds.append("wait $PID{}\n".format(i % n_threads))
