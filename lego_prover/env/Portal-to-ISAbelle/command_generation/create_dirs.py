import os

saving_directory = input("Enter the directory to save extractions at:\n").strip()
if not os.path.isdir(saving_directory):
    os.makedirs(saving_directory)

theory_directory = input("Enter the directory to find extractions at:\n").strip()

for file_name in os.listdir(theory_directory):
    create_name = os.path.join(saving_directory, file_name)
    os.mkdir(create_name)
