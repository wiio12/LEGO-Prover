from PisaFlexibleClient import initialise_env


theorem2 = """theory FunWithFunctions imports Complex_Main begin
theorem 1: 
  fixes f:: "real \<Rightarrow> real"
    and g:: "real \<Rightarrow> real"
  assumes "\<forall> x. f x = 3 * x - 8"
    and "\<forall> x. g (f x) = 2 * x powr 2 + 5 * x - 3"
  shows "g (-5) = 4"
proof -
  have "f 1 = -5" 
    by (simp add: assms(1))
  then have "g (-5) = g (f 1)" 
    by auto
  then show ?thesis 
    by (simp add: assms(2))
qed"""

theorem2_sledgehammer = """theory NA imports Main begin
theorem 1: "1+2=3"
proof -
  show ?thesis 
  sledgehammer
qed"""

def get_parsed(env, theory, tls_name='default'):
    # env.reset()
    env.post('<initialise>')
    steps = env.post(f"<parse text> ${theory}")
    return steps.split('<SEP>')

def run_proof_example(env, steps, tls_name='default'):
    # env.reset()
    env.post('<initialise>')

    for i, step in enumerate(steps):
        print("(%d) %s" % (i, step))
        obs, reward, done, metadata = env.step_to_top_level_state(
            action=step,
            tls_name=tls_name,
            new_name=tls_name
        )
        print("\tobs: %s\n\treward: %s\n\tdone: %s" % (obs, reward, done))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--isa-path', default='/private/home/aqj/Isabelle2021')
    parser.add_argument('--working-dir', default='/private/home/aqj/afp-2021-10-22/thys/FunWithFunctions')
    parser.add_argument('--theory-file', default='/private/home/aqj/afp-2021-10-22/thys/FunWithFunctions/FunWithFunctions.thy')

    args = parser.parse_args()

    # import ipdb; ipdb.set_trace(context=20)
    env = initialise_env(9000,
        working_directory=args.working_dir,
        isa_path=args.isa_path,
        theory_file_path=args.theory_file
    )
    steps = get_parsed(env, theorem2)
    
    steps = [step for step in steps if step!="$"]
    print(steps)
    
    new_env = initialise_env(9000,
        working_directory=args.working_dir,
        isa_path=args.isa_path,
        theory_file_path=args.theory_file
    )
    run_proof_example(new_env, steps)

    # print(env.post("<get_ancestors>"))