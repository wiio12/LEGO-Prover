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
    engine_id = input("What engine id to use? (starting https: and ending with completions) (blank and will use small model by default)\n").strip()
    if (len(engine_id) == 0):
        engine_id = ""

    script = 'echo "y" | sbt "runMain pisa.agent.HPSearch {} {} {} {} {} {} {} {} {} {} {} {}"'

    max_tokens = 128
    max_trials = 200
    timeout = 240000
    search_width = 32
    total_cmds = list()
    mql_sweep = [8, 16, 32]
    for temperature in [0.7, 0.8, 1.0, 1.2]:
        for maximum_queue_length in mql_sweep:
            if use_quick_ones.startswith("t") or use_quick_ones.startswith("T"):
                pattern = "universal_test_theorems/quick_test_name_*.json"
            else:
                pattern = "universal_test_theorems/test_name_*.json"

            results_dir = ""
            if use_conj.startswith("t"):
                results_dir = "results/search_eval_conj_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}".format(
                    search_width, maximum_queue_length, temperature, max_tokens, max_trials, timeout)
            elif use_proof.startswith("t"):
                results_dir = "results/search_eval_proof_and_state_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}".format(
                    search_width, maximum_queue_length, temperature, max_tokens, max_trials, timeout)
            else:
                results_dir = "results/search_eval_state_only_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}".format(
                    search_width, maximum_queue_length, temperature, max_tokens, max_trials, timeout)

            if os.path.isdir(results_dir):
                shutil.rmtree(results_dir)
            os.makedirs(results_dir)

            for file_name in glob.glob(pattern, recursive=True):
                total_cmds.append(script.format(file_name, use_proof, use_conj, use_state_first, results_dir,
                                                search_width, maximum_queue_length, temperature, max_tokens, max_trials, timeout, engine_id))

    process_number_to_cmds = {i: [] for i in range(number_of_processes)}
    for i, cmd in enumerate(total_cmds):
        process_number_to_cmds[i%number_of_processes].append(cmd)

    for process_number, process_cmds in process_number_to_cmds.items():
        with open("scripts/eval_search_conj_{}_use_proof_{}_use_state_first_{}_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}_{}.sh".format(
                use_conj, use_proof, use_state_first, search_width, "sweep_{}".format("_".join([str(element) for element in mql_sweep])), temperature, max_tokens, max_trials, timeout, process_number), "w") as f:
            for process_cmd in process_cmds:
                f.write(process_cmd+"\n")
                f.write("PIDmain=$!\n")
                f.write("wait $PIDmain\n")


deduplication
