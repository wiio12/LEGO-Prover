ports = str(input("Enter the ports, separated by commas:\n")).strip()
ports = ports.split(",")
ports = [int(port.strip()) for port in ports]
ports = [port for port in ports if port]
use_hammers = str(input("Use hammers (T/F):\n")).strip()
if use_hammers == "T" or use_hammers == "t":
    use_hammers = True
elif use_hammers == "F" or use_hammers == "f":
    use_hammers = False
else:
    raise AssertionError

import glob
import os
import shutil

home_directory = "/private/home/aqj"

script = f"unset http_proxy; unset https_proxy; python3 src/main/python/one_stage_extraction.py  --isa-path {home_directory}/Isabelle2021 -wd {home_directory}" + "/afp-2021-10-22/thys/{} --saving-directory afp_extractions/{} -tfp {}"
if use_hammers:
    script = script + " -us"

n_threads = 1

cmds = []

IGNORED_THEORIES = {}
IGNORED_ENTRIES = {}

total_files = 0
for project_name in glob.glob("{}/afp-2021-10-22/thys/**/*.thy".format(home_directory), recursive=True):
    project_single_name = project_name.split("/")[6]
    file_single_name = project_name.split("/")[-1]

    # Ignore already extracted files
    if os.path.isfile("afp_extractions/{}/{}_ground_truth.json".format(
            project_single_name, file_single_name.split(".thy")[0])):
        continue

    if project_single_name not in IGNORED_ENTRIES and \
            project_single_name + "/" + file_single_name not in IGNORED_THEORIES:
        cmds.append(
            script.format(project_single_name, project_single_name, project_name))
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

if os.path.isdir("scripts/extraction"):
    shutil.rmtree("scripts/extraction")

os.makedirs("scripts/extraction")

counter = 0
for j, port in enumerate(ports):
    port_cmds = cmds_for_port[port]
    for i, cmd in enumerate(port_cmds):
        with open(f"scripts/extraction/script_{j}.sh", "a") as f:
            f.write('unset http_proxy; unset https_proxy; sbt "runMain pisa.server.PisaOneStageServer{}"&\n'.format(port))
            f.write("PIDmain=$!\n")
            f.write("sleep 12\n")
            f.write(cmd + "&\n")
            f.write("PID=$!\n")
            f.write("wait $PID\n")
            f.write("rm -rf target/bg-jobs \n")
            f.write("kill $PIDmain\n")
        counter += 1


    #
    # with open("afp_extract_script_{}.sh".format(port), "w") as f:
    #     f.write('sbt "runMain pisa.server.PisaOneStageServer{}"&\n'.format(port))
    #     f.write("PIDmain=$!\n")
    #     f.write("sleep 12\n")
    #     wait_cmds = []
    #     for i, cmd in enumerate(port_cmds):
    #         if (i + 1) % n_threads == 0:
    #             f.write(cmd + "&\n")
    #             f.write("PID{}=$!\n".format(i % n_threads))
    #             wait_cmds.append("wait $PID{}\n".format(i % n_threads))
    #             for wait in wait_cmds:
    #                 f.write(wait)
    #             wait_cmds = []
    #             # f.write("ps aux | grep scala | awk '{print $2}' | xargs kill\n")
    #             # f.write("ps aux | grep java | awk '{print $2}' | xargs kill\n")
    #             # f.write("ps aux | grep poly | awk '{print $2}' | xargs kill\n")
    #             f.write("kill $PIDmain\n")
    #             if (i+1) % 20 == 0:
    #                 f.write("rm -rf target/bg-jobs/* \n")
    #             f.write('sbt "runMain pisa.server.PisaOneStageServer{}" &\n'.format(port))
    #             f.write("PIDmain=$!\n")
    #             f.write("sleep 12\n")
    #         else:
    #             f.write(cmd + "&\n")
    #             f.write("PID{}=$!\n".format(i % n_threads))
    #             wait_cmds.append("wait $PID{}\n".format(i % n_threads))
