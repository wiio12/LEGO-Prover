import os

basic_command = "/home/ywu/Isabelle2020/bin/isabelle build -b -d /home/ywu/Isabelle2020/src/{} \n"

strings_to_write = []
thy_dir = "/home/ywu/Isabelle2020/src"
for project in os.listdir(thy_dir):
    if os.path.isdir(os.path.join(thy_dir, project)):
        strings_to_write.append(basic_command.format(project))

print("{} projects in total".format(len(strings_to_write)))

with open("build_isabelle_std.sh", "w") as fout:
    for string_to_write in strings_to_write:
        fout.write(string_to_write)
