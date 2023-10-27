from PisaFlexibleClient import IsaFlexEnv

import os


if __name__ == "__main__":
    isa_path = input("Path to Isabelle (default /home/qj213/Isabelle2021): ")
    isa_path = "/home/qj213/Isabelle2021" if not isa_path else isa_path.strip()
    afp_path = input("Path to the working directory (default /home/qj213/Isabelle2021/src/HOL/Examples): ")
    afp_path = "/home/qj213/Isabelle2021/src/HOL/Examples" if not afp_path else afp_path.strip()
    file_path = input("Path to a theory file (default /home/qj213/Isabelle2021/src/HOL/Examples/Drinker.thy): ")
    file_path = "/home/qj213/Isabelle2021/src/HOL/Examples/Drinker.thy" if not file_path else file_path.strip()
    env = IsaFlexEnv(
        port=8000, isa_path=isa_path, starter_string=file_path,
        working_directory=afp_path,
    )

    while True:
        proof_step = input("Your chosen proof step ('<fin>' to exit): ")
        if proof_step.strip().startswith("<fin>"):
            break
        obs, rewards, done, _ = env.step(proof_step)
        print(obs)
