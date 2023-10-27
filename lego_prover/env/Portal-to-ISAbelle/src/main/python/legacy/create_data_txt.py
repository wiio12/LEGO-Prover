import os
import argparse
import random
from smart_open import open
from tqdm import tqdm


# Token id: 14457; token: Cambridge
# We use this token to separate the source and the target
# It's unlikely to appear in the Isabelle proof corpus as it's the name of a place
# Token id: 50256; token <|endoftext|>

def process(src_path, tgt_path, output_path, mode):
    random.seed(0)
    if not output_path.startswith('gs://'):
        os.makedirs(os.path.dirname(output_path), exist_ok=True)

    with open(src_path) as src_fhand, open(tgt_path) as tgt_fhand, open(
            output_path, "w") as output_fhand:
        src_lines = src_fhand.readlines()
        tgt_lines = tgt_fhand.readlines()

        total_lines = len(src_lines)
        random_order = list(range(total_lines))
        random.shuffle(random_order)
        for index in tqdm(random_order):
            src_line = src_lines[index]
            tgt_line = tgt_lines[index]

            if mode == "state_only":
                output_fhand.write(src_line.strip().replace("State:",
                                                            "<ISA_OBS>") + " Cambridge " + tgt_line.strip() + " <|endoftext|> ")
            elif mode == "proof_only":
                output_fhand.write(src_line.strip().replace("Proof:", "<ISA_PRF>") + " Cambridge " + tgt_line.strip() + " <|endoftext|> ")
            elif mode == "proof_and_state":
                output_fhand.write(
                    src_line.strip().replace("<PS_SEP> State:",
                                             "<ISA_OBS>").replace("Proof:",
                                                                  "<ISA_PRF>")
                    + " Cambridge " + tgt_line.strip() + " <|endoftext|> "
                )
            else:
                output_fhand.write(src_line.strip() + " Cambridge " + tgt_line.strip() + " <|endoftext|> ")


def create_data(data_dir, output_dir, name, mode):
    train_src_path = os.path.join(data_dir, "train.src")
    train_tgt_path = os.path.join(data_dir, "train.tgt")
    # assert name in ["state_only", "proof_only", "proof_and_state"]
    train_output_path = os.path.join(output_dir,
                                     "train", "{}_train.txt".format(name))
    val_src_path = os.path.join(data_dir, "val.src")
    val_tgt_path = os.path.join(data_dir, "val.tgt")
    val_output_path = os.path.join(output_dir,
                                   "val", "{}_val.txt".format(name))
    process(train_src_path, train_tgt_path, train_output_path, mode=mode)
    process(val_src_path, val_tgt_path, val_output_path, mode=mode)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Create the .txt files for fine-tuning from the raw PISA src-tgt pairs.")
    parser.add_argument("--data-dir", type=str, default="",
                        help="Input directory (default: current directory)")
    parser.add_argument("--output-dir", type=str, default="/home/qj213/data",
                        help="Output directory (default: home data directory)")
    parser.add_argument("--name", type=str,
                        help="Name of the currently processed data.")
    parser.add_argument("--mode", type=str,
                        help="mode of the currently processed data (state_only, proof_only, proof_and_state, custom).")
    args = parser.parse_args()
    create_data(args.data_dir, args.output_dir, args.name, args.mode)
