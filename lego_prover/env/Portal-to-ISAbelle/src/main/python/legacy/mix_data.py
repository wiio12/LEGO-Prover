import argparse
import os


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Mix the data from multiple forms of input")
    parser.add_argument("--input", type=str, nargs="+", help="Input files")
    parser.add_argument("--output-path", "-op", type=str, help="Output file")
    args = parser.parse_args()

    for output_file_name in ["train.src", "train.tgt", "val.src", "val.tgt", "test.src", "test.tgt"]:
        if os.path.isfile(os.path.join(args.output_path, output_file_name)):
            os.remove(os.path.join(args.output_path, output_file_name))

    for input_path in args.input:
        for output_file_name in ["train.src", "train.tgt", "val.src", "val.tgt", "test.src", "test.tgt"]:
            with open(os.path.join(args.output_path, output_file_name), "a") as output_file, \
                    open(os.path.join(input_path, output_file_name), "r") as input_file:
                output_file.write(input_file.read())
