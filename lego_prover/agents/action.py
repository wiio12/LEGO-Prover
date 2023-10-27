from copy import copy
import os
import random
import re
import time

import lego_prover.utils as U
from langchain.prompts import SystemMessagePromptTemplate, HumanMessagePromptTemplate
from langchain.schema import AIMessage, HumanMessage, SystemMessage

from lego_prover.prompts import load_prompt

from lego_prover.utils.langchain_utils import LLMMixture

class ActionAgent:
    def __init__(
        self,
        logger=None,
        model_name="gpt-3.5-turbo",
        temperature=0,
        request_timeout=120,
        ckpt_dir="ckpt",
    ):
        self.logger = logger
        self.ckpt_dir = ckpt_dir
        U.f_mkdir(f"{ckpt_dir}/action")
        self.llm = LLMMixture(
            model_name=model_name,
            temperature=temperature,
            request_timeout=request_timeout,
        )

        # load decomposer examples:
        self.decomposer_examples = {}
        for file in os.listdir("data/decomposer_examples"):
            with open(os.path.join("data/decomposer_examples", file), "r") as f:
                text = f.read()
            self.decomposer_examples[file[:-4]] = text
        
        self.formalizer_examples = {}
        for file in os.listdir("data/formalizer_examples"):
            with open(os.path.join("data/formalizer_examples", file), "r") as f:
                text = f.read()
            self.formalizer_examples[file[:-4]] = text
    
    def retrieved_example_skills(self, retrieved_skills):
        random.shuffle(retrieved_skills)
        prompt_examples = []
        for ix, skills in enumerate(retrieved_skills):
            skill_code = skills["code"]
            prompt_example = f"""###### useful skill {ix+1}: ######
```isabelle
{skill_code}
```
"""
            prompt_examples.append(prompt_example)
        
        example_programmes = "\n\n".join(prompt_examples)
        return example_programmes
    
    def decomposer(self, context):
        system_prompt_template = load_prompt("decomposer")
        system_message = SystemMessage(content=system_prompt_template)

        human_prompt_template = load_prompt("decomposer_human")
        human_prompt_template = HumanMessagePromptTemplate.from_template(human_prompt_template)

        # post-process in-context-learning examples
        decomposer_examples = copy(self.decomposer_examples)
        if context["problem_name"] in decomposer_examples:
            decomposer_examples.pop(context["problem_name"])
        icl_examples = random.sample(list(decomposer_examples.values()), 3)
        icl_examples = "\n\n####################\n\n".join(icl_examples)

        context["informal_statement"] = context["informal_statement"].replace("\n", ' ').strip()
        context["informal_proof"] = context["informal_proof"].replace("\n", " ").strip()

        human_message = human_prompt_template.format(
            examples=icl_examples,
            informal_statement=context["informal_statement"],
            informal_proof=context["informal_proof"],
            formal_statement=context["formal_statement"],
        )

        conversation = {
            "sys0":  system_message.content,
            "human0": human_message.content,
        }

        self.logger.info(
            f"****decomposer system message****\n{system_message.content}"
        )

        self.logger.info(
            f"****decomposer human message****\n{human_message.content}"
        )

        n_retry = 3
        informal_proof = context["informal_proof"]
        skill_requests = []
        while n_retry > 0:
            try:
                ai_message = self.llm([system_message, human_message], temperature=0)
                self.logger.info(
                    f"****decomposer ai message****\n{ai_message.content}"
                )
                conversation[f"ai{3-n_retry}"] = ai_message.content
                message = ai_message.content
                if "####################" in message:
                    message = message[:message.index("####################")]
                # Extracting Error Analysis content
                informal_proof = re.search(r'## Structured informal proof\n(.*?)\n\n#', message, re.DOTALL).group(1).strip()

                # Extracting each skill request's name and its content
                skill_requests = re.findall(r"```isabelle\n(.*?)\n```", message, re.DOTALL)
                break
            except AssertionError as e:
                if "query too long" in str(e):
                    self.logger.warn(str(e))
                    break
            except Exception as e:
                self.logger.info(f"Error occur in decomposer: {str(e)}")
                n_retry -= 1
                examples = random.sample(list(decomposer_examples.values()), 3)
                examples = "\n\n####################\n\n".join(examples)
                human_message = human_prompt_template.format(
                    examples=examples,
                    informal_statement=context["informal_statement"],
                    informal_proof=context["informal_proof"],
                    formal_statement=context["formal_statement"],
                )
                time.sleep(5)
        ret_request = []
        for skill in skill_requests:
            if "N/A" in skill:
                continue
            ret_request.append(skill)

        if len(ret_request) > 5:
            self.logger.info(f"skill request more than 5, with len {len(ret_request)}")
            ret_request = random.sample(ret_request, 5)

        return informal_proof, ret_request, conversation

    def critic(self, context, code_last_round=None, error_last_round=None):
        system_prompt_template = load_prompt("critic_request")
        system_prompt_template = SystemMessagePromptTemplate.from_template(system_prompt_template)
        system_message = system_prompt_template.format(examples="")

        human_prompt_template = load_prompt("critic_request_human")
        human_prompt_template = HumanMessagePromptTemplate.from_template(human_prompt_template)

        if code_last_round is None:
            code_last_round = "No code from last round..."
        else:
            code_last_round = code_last_round.split('\n')
            new_code = []
            for ix, line in enumerate(code_last_round):
                line = f"#{ix+1} " + line
                new_code.append(line)
            code_last_round = "\n".join(new_code)
        
        if error_last_round is None:
            error_last_round = "No error from last round..."

        human_message = human_prompt_template.format(
            code=code_last_round,
            error=error_last_round,
        )

        # self.logger.info(
        #     f"****critic agent system message****\n{system_message.content}"
        # )

        self.logger.info(
            f"****critic agent human message****\n{human_message.content}"
        )

        n_retry = 3
        error_analysis = "No error analysis..."
        skill_requests = []
        while n_retry > 0:
            try:
                ai_message = self.llm([system_message, human_message])
                self.logger.info(
                    f"****critic agent ai message****\n{ai_message.content}"
                )
                message = ai_message.content
                # Extracting Error Analysis content
                error_analysis = re.search(r'# Error analysis:\n(.*?)\n\n#', message, re.DOTALL).group(1).strip()

                # Extracting each skill request's name and its content
                skill_requests = re.findall(r'## Skill \d+: ([\w_]+)\n```isabelle\n(.*?)\n```', message, re.DOTALL)
                break
            except AssertionError as e:
                if "query too long" in str(e):
                    self.logger.warn(str(e))
                    break
            except Exception as e:
                self.logger.info(f"Error occur in auto_formal_pre: {str(e)}")
                n_retry -= 1
                time.sleep(5)

        return error_analysis, skill_requests
    
    def render_formalizer_system_message(self):
        system_template = load_prompt("formalizer")
        return SystemMessage(content=system_template)
    
    def render_formalizer_human_message(
        self,
        skills,
        context,
        informal_proof=None,
        n_example=3,
    ) -> HumanMessage:
        human_prompt_template = load_prompt("formalizer_human")
        human_prompt_template = HumanMessagePromptTemplate.from_template(human_prompt_template)

        formalizer_examples = copy(self.formalizer_examples)
        if context["problem_name"] in formalizer_examples:
            formalizer_examples.pop(context["problem_name"])

        examples = random.sample(list(formalizer_examples.values()), n_example)
        examples = "\n\n####################\n\n".join(examples)
        context["informal_statement"] = context["informal_statement"].replace("\n", ' ').strip()
        context["informal_proof"] = context["informal_proof"].replace("\n", " ").strip()

        skills = self.retrieved_example_skills(skills)
        
        human_message = human_prompt_template.format(
            skill_examples = skills,
            examples=examples,
            informal_statement=context["informal_statement"],
            informal_proof=context["informal_proof"] if informal_proof is None else informal_proof,
            formal_statement=context["formal_statement"],
        )

        return human_message


    def render_human_message(
        self, 
        context, 
        code=None,
        error=None,
        error_analysis=None,
        informal_proof=None,
    ) -> HumanMessage:
        human_prompt_template = load_prompt("auto_formal2_human")
        human_prompt_template = HumanMessagePromptTemplate.from_template(human_prompt_template)

        if code is None:
            code = "No code from last round..."
        else:
            code = code.split('\n')
            new_code = []
            for ix, line in enumerate(code):
                line = f"#{ix+1} " + line
                new_code.append(line)
            code = "\n".join(new_code)
        
        if error is None:
            error = "No error from last round..."
        if error_analysis is None:
            error_analysis = "No analysis..."

        human_message = human_prompt_template.format(
            informal_statement=context["informal_statement"],
            informal_proof=context["informal_proof"] if informal_proof is None else informal_proof,
            formal_statement=context["formal_statement"],
            code_last_round=code,
            error_last_round=error,
            error_analysis=error_analysis,
        )

        return human_message

    def process_ai_message(self, message, context):
        assert isinstance(message, AIMessage)

        retry = 3
        error = None
        while retry > 0:
            try:
                code_pattern = re.compile(r"```(?:[i|I]sabelle)(.*?)```", re.DOTALL)
                text = message.content[message.content.index("# Formalized Code"):]
                code = "\n".join(code_pattern.findall(text)).strip()
                return code
            except Exception as e:
                retry -= 1
                error = e
                time.sleep(1)
        self.logger.info(f"Error parsing action response (before program execution): {error}")
        return False

