from pisa_client import initialise_env


if __name__ == '__main__':
    env = initialise_env(
        8001, 
        "/home/qj213/Isabelle2022", 
        "/home/qj213/afp-2022-12-06/thys/Real_Impl/Real_Impl_Auxiliary.thy", 
        "/home/qj213/afp-2022-12-06/thys/Real_Impl"
    )
    env.proceed_to_line('end', 'before')
    env.initialise()
    print(env.step_to_top_level_state('lemma primes_infinite: "\<not> (finite {(p::nat). prime p})"', "default", "test"))
    print(env.step_to_top_level_state('normalhammer', 'test', 'test1'))
    print(env.step_to_top_level_state('normalhammer <del>primes_infinite<del>', 'test', 'test2'))
    print(env.step_to_top_level_state('normalhammer <del>primes_infinite,bigger_prime<del>', 'test', 'test3'))
    print(env.step_to_top_level_state('normalhammer <add>next_prime_bound<add> <del>primes_infinite,bigger_prime<del>', 'test', 'test4'))
