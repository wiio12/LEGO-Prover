import argparse


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Get the ")
    parser.add_argument("--path-to-proof-and-state-file", "-ptpasf", type=str, help="Path to the file of the proof steps and states.")
    args = parser.parse_args()

    lengths = list()
    with open(args.path_to_proof_and_state_file) as fin:
        for line in fin.readlines():
            lengths.append(len(line.strip()))
            
    maximum_sequence_length_in_chars = 256 * 3

    print(f"Minimum: {min(lengths)}")
    print(f"Maximum: {max(lengths)}")
    print(f"Average: {sum(lengths)/len(lengths)}")
    print(f"Median: {sorted(lengths)[int(len(lengths)/2)]}")
    print(f"Retainment rate: {sorted(lengths + [maximum_sequence_length_in_chars]).index(maximum_sequence_length_in_chars) / (len(lengths)+1)}")