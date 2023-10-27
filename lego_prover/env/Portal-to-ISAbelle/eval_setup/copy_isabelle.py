import argparse
import shutil
import os
from tqdm import tqdm


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--isabelle", type=str, required=True)
    parser.add_argument("--isabelle-user", type=str, required=True)
    parser.add_argument("--number-of-copies", type=int, required=True)
    parser.add_argument("--output-path", type=str, required=True)
    args = parser.parse_args()

    isabelle_identifier = args.isabelle.split("/")
    isabelle_identifier = isabelle_identifier[-1] if isabelle_identifier[-1] else isabelle_identifier[-2]

    for index in tqdm(range(args.number_of_copies)):
        index_path = os.path.join(args.output_path, f"isabelle_copy_{index}")
        if not os.path.exists(index_path):
            os.makedirs(index_path)

        main_isa_path = os.path.join(index_path, "main_isa")
        if not os.path.exists(main_isa_path):
            os.makedirs(main_isa_path)
        shutil.copytree(args.isabelle, os.path.join(main_isa_path, isabelle_identifier), symlinks=True)

        user_isa_path = os.path.join(index_path, "user_isa")
        if os.path.exists(user_isa_path):
            raise AssertionError
        shutil.copytree(args.isabelle_user, user_isa_path, symlinks=True)

        # Edit the settings file such that the user home points to the right directory
        original_isabelle_home_user_string = "$USER_HOME/.isabelle"
        isabelle_home_user_string = str(user_isa_path)
        
        isabelle_settings_path = os.path.join(main_isa_path, isabelle_identifier, "etc/settings")
        with open(isabelle_settings_path, "r") as f:
            settings = f.read()
        settings = settings.replace(original_isabelle_home_user_string, isabelle_home_user_string)
        with open(isabelle_settings_path, "w") as f:
            f.write(settings)
