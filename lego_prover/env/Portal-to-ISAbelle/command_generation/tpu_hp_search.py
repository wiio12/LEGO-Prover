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
    using_t5 = input("Are you using a T5 server? (true/false)?\n").strip()
    greedy = input("Are you using greedy search? (true/false)?\n").strip()
    last_k = input("How many last steps to incldue as context (>=0, 0 to disable)?\n").strip()
    needed = input("Are you using needed steps as context (true/false)?\n").strip()


    # script = 'echo "y" | sbt "runMain pisa.agent.TPUHPSearch {} {} {} {} {} {} {} {} {} {} {} {}"'

    max_tokens = 64
    max_trials = 100
    timeout = 6000000
    search_width = 8
    total_cmds = list()
    mql_sweep = 16
    temperature = 1.0
    # if using_t5.startswith("t"):
    #     using_t5 = "true"
    # else:
    #     using_t5 = "false
    

    results_dir = ""
    if use_conj.startswith("t"):
        results_dir = "results/search_eval_conj_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}_usingT5_{}_greedy_{}_last_{}_needed_{}".format(
            search_width, mql_sweep, temperature, max_tokens, max_trials, timeout, using_t5, greedy, last_k, needed)
    elif use_proof.startswith("t"):
        results_dir = "results/search_eval_proof_and_state_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}_usingT5_{}_greedy_{}_last_{}_needed_{}".format(
            search_width, mql_sweep, temperature, max_tokens, max_trials, timeout, using_t5, greedy, last_k, needed)
    else:
        results_dir = "results/search_eval_state_only_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}_usingT5_{}_greedy_{}_last_{}_needed_{}".format(
            search_width, mql_sweep, temperature, max_tokens, max_trials, timeout, using_t5, greedy, last_k, needed)

    if os.path.isdir(results_dir):
        shutil.rmtree(results_dir)
    os.makedirs(results_dir)

    if use_quick_ones.startswith("t") or use_quick_ones.startswith("T"):
        pattern = "universal_test_theorems/quick_test_name_{}.json"
        for i in range (1, 301):
            total_cmds.append(
                f'echo "y" | sbt "runMain pisa.agent.TPUHPSearch {pattern.format(i)} {use_proof} {use_conj} {use_state_first} {results_dir} ' 
                f'{search_width} {mql_sweep} {temperature} {max_tokens} {max_trials} {timeout} {using_t5} '
                f'{greedy} {last_k} {needed}"'
            )
    else:
        pattern = "universal_test_theorems/test_name_{}.json"
        for i in range (1, 3001):
            total_cmds.append(
                f'echo "y" | sbt "runMain pisa.agent.TPUHPSearch {pattern.format(i)} {use_proof} {use_conj} {use_state_first} {results_dir} ' 
                f'{search_width} {mql_sweep} {temperature} {max_tokens} {max_trials} {timeout} {using_t5} '
                f'{greedy} {last_k} {needed}"'
            )
    
    process_number_to_cmds = {i: [] for i in range(number_of_processes)}
    for i, cmd in enumerate(total_cmds):
        process_number_to_cmds[i%number_of_processes].append(cmd)

    for process_number, process_cmds in process_number_to_cmds.items():
        with open("scripts/eval_search_conj_{}_use_proof_{}_use_state_first_{}_search_width_{}_maximum_queue_length_{}_temperature_{}_max_tokens_{}_max_trials_{}_timeout_{}_usingT5_{}_greedy_{}_last_{}_needed_{}_{}.sh".format(
                use_conj, use_proof, use_state_first, search_width, "sweep_{}".format(mql_sweep), temperature, max_tokens, max_trials, timeout, using_t5, greedy, last_k, needed, process_number), "w") as f:
            for process_cmd in process_cmds:
                f.write(process_cmd+"\n")
                f.write("PIDmain=$!\n")
                f.write("wait $PIDmain\n")
