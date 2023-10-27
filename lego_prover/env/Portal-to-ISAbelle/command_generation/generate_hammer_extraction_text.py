import glob
import os
for i, file_path in enumerate(glob.glob("/home/qj213/afp-2021-10-22/thys/**/*.thy", recursive=True)):
    with open(f"data/hammer_extraction_{i}.txt", "w") as fout:
        fout.write(f"{file_path}\n")