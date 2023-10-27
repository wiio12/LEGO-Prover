if __name__ == "__main__":
    import argparse
    import os
    import json
    parser = argparse.ArgumentParser(description="Convert Scala dump to test name JSONs.")
    parser.add_argument("--scala-dump-path", required=True, help="Scala dump path.")
    args = parser.parse_args()

    for file in os.listdir(args.scala_dump_path):
        if file.startswith("test_name_"):
            with open(os.path.join(args.scala_dump_path, file), "r") as f:
                lines = f.read().strip()
                thy_path, theorem_decl = lines.split("\n")
                json.dump([[thy_path, theorem_decl]], open(os.path.join(args.scala_dump_path, file+".json"), "w"))
