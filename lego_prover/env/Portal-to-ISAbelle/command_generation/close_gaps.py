import argparse
import os


starter = """#!/bin/bash
#SBATCH --job-name=myJobarrayTest
#SBATCH --nodes=1 --ntasks=1
#SBATCH --time=5:00
#SBATCH --output=test_%A_%a.out
#SBATCH --error=test_%A_%a.err
#SBATCH --partition cpu
#SBATCH --array=0-4

commands=(\n"""

finisher = """);

sbt "runMain ${commands[$SLURM_ARRAY_TASK_ID]}"
"""

if __name__ == "__main__":
    args = argparse.ArgumentParser()
    args.add_argument("-i", "--input_directory", 
            help="Where to look for the input thy files", required=True)
    args.add_argument("-o", "--output_path",
            help="Path to put the output shell file", required=True)
    args.add_argument("-d", "--dump_path",
            help="Where to dump the results", required=True)
    args.add_argument("-ip", "--isabelle_path",
            help="Where is Isabelle", required=False)
    args = args.parse_args()


    list_of_files = []
    for file in os.listdir(args.input_directory):
        if file.endswith(".thy"):
            list_of_files.append(os.path.join(file))

    with open(args.output_path, "w") as output_file:
        output_file.write(starter)
        for file in list_of_files:
            dump_path = os.path.join(args.dump_path, f"{file.split('/')[-1]}.result")
            output_file.write(f"\"{args.isabelle_path} {args.input_directory} {file} {dump_path}\"\n")
        output_file.write(finisher)
