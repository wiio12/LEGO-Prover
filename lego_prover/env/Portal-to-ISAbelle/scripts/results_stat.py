import os
import sys

def stats_from_an_exp(exp_folder):
    total = 0
    correct = 0
    for file_name in os.listdir(exp_folder):
        if file_name.startswith("test_result"):
            theorem_number = int(file_name.split("_")[-1])
            total += 1
            correct += float(open(os.path.join(exp_folder, file_name)).read())

    print("Total: ", total)
    success = 0
    timeout = 0
    fuelout = 0
    queueout = 0
    total = 0
    for file_name in os.listdir(exp_folder):
        if file_name.startswith("test_cause"):
            total += 1
            test_cause = open(os.path.join(exp_folder, file_name)).read()
            if test_cause.startswith("Proved"):
                success += 1
            elif test_cause.startswith("Overall"):
                timeout += 1
            elif test_cause.startswith("Out"):
                fuelout += 1
            elif test_cause.startswith("Queue"):
                queueout += 1
            else:
                raise NotImplementedError
    print("Success | timeout | out of fuel | queue empty proportion:\n {} | {} | {} | {}".format(
        success/total, timeout/total, fuelout/total, queueout/total
    ))


all_folders = True
for file_name in os.listdir(sys.argv[1]):
    if not file_name.startswith("."):
        if not os.path.isdir(os.path.join(sys.argv[1], file_name)):
            all_folders = False

if not all_folders:
    print(sys.argv[1])
    stats_from_an_exp(sys.argv[1])
else:
    for file_name in os.listdir(sys.argv[1]):
        try:
            stats_from_an_exp(os.path.join(sys.argv[1], file_name))
        except:
            pass
