import glob
import os
import shutil

if __name__ == "__main__":
    number_of_processes = input("Enter the number of processes you want to run at the same time:\n").strip()
    number_of_processes = int(number_of_processes)
    use_proof = input("Want to condition on the proof? (true/false)\n").strip()
    use_conj = input("Want to conjecture? (true/false)\n").strip()
    use_quick_ones = input("Want to use quick ones? (true/false)\n").strip()
    use_state_first = input("Want to use the state-only agent for the first step? (true/false) (false recommended)\n").strip()

    use_default = input("What to use default hyperparameters? (true/false)\n").strip()
    if use_default.startswith("true"):
        search_width = 32
        maximum_queue_length = 32
        temperature = 0.8
        max_tokens = 128
        max_trials = 200
        timeout = 240000
    else:
        search_width = int(input("search_width:\n"))
        maximum_queue_length = int(input("maximum_queue_length:\n"))
        temperature = float(input("temperature:\n"))
        max_tokens = int(input("max_tokens:\n"))
        max_trials = int(input("max_trials:\n"))
        timeout = int(input("timeout:\n"))

    script = 'echo "y" | sbt "runMain pisa.agent.OracleAgent {} {} {} {} {} {} {} {} {} {} {}"'

    total_cmds = list()
    if use_quick_ones.startswith("t") or use_quick_ones.startswith("T"):
        pattern = "1000_train_theorems/train_theorem_*.json"
    else:
        pattern = "1000_train_theorems/train_theorem_*.json"

    results_dir = "oracle_results"

    if os.path.isdir(results_dir):
        shutil.rmtree(results_dir)
    os.makedirs(results_dir)

    for file_name in glob.glob(pattern, recursive=True):
        total_cmds.append(script.format(file_name, use_proof, use_conj, use_state_first, results_dir,
                                        search_width, maximum_queue_length, temperature, max_tokens, max_trials, timeout))

    process_number_to_cmds = {i: [] for i in range(number_of_processes)}
    for i, cmd in enumerate(total_cmds):
        process_number_to_cmds[i%number_of_processes].append(cmd)

    for process_number, process_cmds in process_number_to_cmds.items():
        with open("scripts/oracle_{}.sh".format(process_number), "w") as f:
            for process_cmd in process_cmds:
                f.write(process_cmd+"\n")
                f.write("PIDmain=$!\n")
                f.write("wait $PIDmain\n")
