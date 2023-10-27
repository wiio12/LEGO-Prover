import argparse
import shutil
import os
from tqdm import tqdm


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--pisa-jar-path", type=str, required=True)
    parser.add_argument("--number-of-jars", type=int, required=True)
    parser.add_argument("--output-path", type=str, required=True)
    args = parser.parse_args()

    for index in tqdm(range(args.number_of_jars)):
        shutil.copy2(
            args.pisa_jar_path,
            os.path.join(args.output_path, f"pisa_copy{index}.jar")
        )
