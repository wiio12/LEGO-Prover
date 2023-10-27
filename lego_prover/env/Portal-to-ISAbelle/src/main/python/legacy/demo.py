from PisaFlexibleClient import initialise_env

# Run a server on port 8000
# i.e. do a 'sbt "runMain pisa.server.PisaOneStageServer8000"'


env = initialise_env(8000, 
        working_directory="/private/home/aqj/afp-2021-10-22/thys/FunWithFunctions",
        isa_path="/private/home/aqj/Isabelle2021", 
        theory_file_path="/private/home/aqj/afp-2021-10-22/thys/FunWithFunctions/FunWithFunctions.thy"
    )


# Suppose you have a list of theorems that you want to try on
theorems = [
    'theorem identity1: fixes f :: "nat \<Rightarrow> nat" assumes fff: "\<And>n. f(f(n)) < f(Suc(n))" shows "f(n) = n"',
    'theorem ifac_neg0: fixes ifac :: "int \<Rightarrow> int" assumes ifac_rec: "\<And>i. ifac i = (if i=0 then 1 else i*ifac(i - 1))" shows "i<0 \<Longrightarrow> ifac i = 0"'
]
# And the corresponding scripts
scripts = [
    "sorry",
    "bad script"
]

env.post("<initialise>")
for theorem, script in zip(theorems, scripts):
    # Execute before the theorem
    env.post(
        f"<accumulative step before> {theorem}"
    )

    # Create an experimental state with a name e.g. script[-10:]
    # Execute the theorem declaration
    name = script[-10:]
    env.post(
        f"<clone> default <clone> {name}"
    )
    env.post(
        f"<apply to top level state> {name} <apply to top level state> {theorem} <apply to top level state> {name}"
    )
    
    # Execute the script and get the proof level
    response = env.post(
        f"<apply to top level state> {name} <apply to top level state> {script} <apply to top level state> {name}"
    )
    print(f"script execution response: {response}")
    level = env.post(f"<get_proof_level> {name}")
    # If level = 0, succeed, other wise fail
    print(level)
