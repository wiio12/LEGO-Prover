import pkg_resources
import lego_prover.utils as U


def load_prompt(prompt):
    package_path = pkg_resources.resource_filename("lego_prover", "")
    return U.load_text(f"{package_path}/prompts/{prompt}.txt")

def load_context(problem_path):
    return U.load_json(problem_path)
