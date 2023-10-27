from tqdm import tqdm


def fill_dict_state_only(file1, file2, dictionary):
    with open(file1) as fsrc:
        with open(file2) as ftgt:
            src_lines = fsrc.readlines()
            tgt_lines = ftgt.readlines()

            print(src_lines[0])
            print(tgt_lines[0])

            for i in tqdm(range(len(src_lines))):
                src_line = src_lines[i].strip()
                tgt_line = tgt_lines[i].strip()

                src_line = src_line.replace("State:", "[IS] GOAL") + " PROOFSTEP"

                if src_line in dictionary:
                    if tgt_line in dictionary[src_line]:
                        pass
                    else:
                        dictionary[src_line].append(tgt_line)
                else:
                    dictionary[src_line] = [tgt_line]
    return dictionary


def fill_dict_proof_and_state(file1, file2, dictionary):
    with open(file1) as fsrc:
        with open(file2) as ftgt:
            src_lines = fsrc.readlines()
            tgt_lines = ftgt.readlines()

            print(src_lines[0])
            print(tgt_lines[0])

            for i in tqdm(range(len(src_lines))):
                src_line = src_lines[i].strip()
                tgt_line = tgt_lines[i].strip()

                src_line = src_line.replace("Proof:", "[IS] PROOF").replace("State", "[IS] GOAL") + " PROOFSTEP"

                if src_line in dictionary:
                    if tgt_line in dictionary[src_line]:
                        pass
                    else:
                        dictionary[src_line].append(tgt_line)
                else:
                    dictionary[src_line] = [tgt_line]
    return dictionary


def fill_dict_conjecture(file1, file2, dictionary):
    with open(file1) as fsrc:
        with open(file2) as ftgt:
            src_lines = fsrc.readlines()
            tgt_lines = ftgt.readlines()

            print(src_lines[0])
            print(tgt_lines[0])

            for i in tqdm(range(len(src_lines))):
                src_line = src_lines[i].strip()
                tgt_line = tgt_lines[i].strip()

                src_line = "[IS] GOAL " + src_line + " PROOFSTEP"

                if src_line in dictionary:
                    if tgt_line in dictionary[src_line]:
                        pass
                    else:
                        dictionary[src_line].append(tgt_line)
                else:
                    dictionary[src_line] = [tgt_line]
    return dictionary

srcs_to_tgts = dict()
srcs_to_tgts = fill_dict_state_only("data/seq2seq/seq2seq_with_state/train.src", "data/seq2seq/seq2seq_with_state/train.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_proof_and_state("data/seq2seq/seq2seq_with_proof_and_state/train.src", "data/seq2seq/seq2seq_with_proof_and_state/train.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_conjecture("data/conjecturer_seq2seq/train.src", "data/conjecturer_seq2seq/train.tgt",
                         srcs_to_tgts)

with open("data/mixture/train.src", "w") as fsrc_out:
    with open("data/mixture/train.tgt", "w") as ftgt_out:
        for src_line, tgt_lines in srcs_to_tgts.items():
            for tgt_line in tgt_lines:
                fsrc_out.write(src_line)
                fsrc_out.write("\n")
                ftgt_out.write(tgt_line)
                ftgt_out.write("\n")

srcs_to_tgts = dict()
srcs_to_tgts = fill_dict_state_only("data/seq2seq/seq2seq_with_state/val.src", "data/seq2seq/seq2seq_with_state/val.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_proof_and_state("data/seq2seq/seq2seq_with_proof_and_state/val.src", "data/seq2seq/seq2seq_with_proof_and_state/val.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_conjecture("data/conjecturer_seq2seq/val.src", "data/conjecturer_seq2seq/val.tgt",
                         srcs_to_tgts)

with open("data/mixture/val.src", "w") as fsrc_out:
    with open("data/mixture/val.tgt", "w") as ftgt_out:
        for src_line, tgt_lines in srcs_to_tgts.items():
            for tgt_line in tgt_lines:
                fsrc_out.write(src_line)
                fsrc_out.write("\n")
                ftgt_out.write(tgt_line)
                ftgt_out.write("\n")

srcs_to_tgts = dict()
srcs_to_tgts = fill_dict_state_only("data/seq2seq/seq2seq_with_state/test.src", "data/seq2seq/seq2seq_with_state/test.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_proof_and_state("data/seq2seq/seq2seq_with_proof_and_state/test.src", "data/seq2seq/seq2seq_with_proof_and_state/test.tgt",
                         srcs_to_tgts)
srcs_to_tgts = fill_dict_conjecture("data/conjecturer_seq2seq/test.src", "data/conjecturer_seq2seq/test.tgt",
                         srcs_to_tgts)

with open("data/mixture/test.src", "w") as fsrc_out:
    with open("data/mixture/test.tgt", "w") as ftgt_out:
        for src_line, tgt_lines in srcs_to_tgts.items():
            for tgt_line in tgt_lines:
                fsrc_out.write(src_line)
                fsrc_out.write("\n")
                ftgt_out.write(tgt_line)
                ftgt_out.write("\n")
