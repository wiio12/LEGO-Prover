import os

basic_command = "Isabelle2020/bin/isabelle build -b -d $AFP {}\n"

strings_to_write = []
thy_dir = "$AFP/thys"
for project in os.listdir(thy_dir):
    if os.path.isdir(os.path.join(thy_dir, project)):
        strings_to_write.append(basic_command.format(project))

print("{} projects in total".format(len(strings_to_write)))

with open("PISA/scripts/build_isabelle_afp.sh", "w") as fout:
    for string_to_write in strings_to_write:
        fout.write(string_to_write)
