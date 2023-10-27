import os
import re

import tiktoken

import lego_prover.utils as U
from lego_prover.env.chromas import ChromaBridge

from lego_prover.utils.langchain_utils import LLMMixture

from difflib import SequenceMatcher, get_close_matches

def similar(a, b):
    return SequenceMatcher(None, a, b).ratio()


class SkillManager:
    def __init__(
        self,
        rank = None,
        logger = None,
        ckpt_dir="ckpt",
        skill_manager_lock=U.WithEmpty(),
        chroma_bridge: ChromaBridge  = None
    ):
        self.rank = rank
        self.logger = logger
        self.skill_manager_lock = skill_manager_lock
        self.chroma_bridge = chroma_bridge
        U.f_mkdir(f"{ckpt_dir}/skill/code")
        U.f_mkdir(f"{ckpt_dir}/skill/history_problem")
        U.f_mkdir(f"{ckpt_dir}/skill/requests")
        U.f_mkdir(f"{ckpt_dir}/skill/description")
        U.f_mkdir(f"{ckpt_dir}/skill/vectordb")
        self.ckpt_dir = ckpt_dir
        self.encoder = tiktoken.encoding_for_model("gpt-4")
        with self.skill_manager_lock:
            self.sync_checkpoint()
    
    def sync_checkpoint(self):
        if os.path.exists(f"{self.ckpt_dir}/skill/skills.json"):
            self.skills = U.load_json(f"{self.ckpt_dir}/skill/skills.json")
        else:
            self.skills = {}
        if os.path.exists(f"{self.ckpt_dir}/skill/codes.json"):
            self.codes = U.load_json(f"{self.ckpt_dir}/skill/codes.json")
        else:
            self.codes = {}
        if os.path.exists(f"{self.ckpt_dir}/skill/skill_request.json"):
            self.skill_requests = U.load_json(f"{self.ckpt_dir}/skill/skill_request.json")
        else:
            self.skill_requests = {}
    
    def add_new_problem(self, problem_name, formal_statement):
        data = ("problem_add_text", {
                "add_text": formal_statement,
                "problem_name": problem_name,
        })
        output = self.chroma_bridge.run_cmd(data)
        assert output["error"] is None, "error is not None"
        print(output["output"])

    def add_new_request(self, problem_name, formal_statement, init_update_count=0):
        with self.skill_manager_lock:
            self.sync_checkpoint()

        exists_formal_statements = [value['formal_statement'] for value in self.skill_requests.values()]
        if len(get_close_matches(formal_statement, exists_formal_statements, n=1, cutoff=0.85)) != 0:
            return

        with self.skill_manager_lock:
            self.sync_checkpoint()
            request_name = f"request_{len(self.skill_requests)}"
            self.skill_requests[request_name] = {
                "request_name": request_name,
                "problem_name": problem_name,
                "formal_statement": formal_statement,
                "update_count": init_update_count,
            }
            

            data = ("request_add_text", {
                "add_text": formal_statement,
                "request_name": request_name,
            })
            
            assert self.chroma_bridge is not None
            output = self.chroma_bridge.run_cmd(data)
            if output["error"] is None:
                # print("There are",  output["output"], "code")
                assert output["output"] == len(
                    self.skill_requests
                ), ("requestdb is not synced with skill_request.json, "
                    f"there are {output['output']} in requestdb but {len(self.skill_requests)} in skill_request.json")
            
            U.dump_text(
                formal_statement, f"{self.ckpt_dir}/skill/requests/{request_name}.thy"
            )
            U.dump_json(self.skill_requests, f"{self.ckpt_dir}/skill/skill_request.json")
            self.logger.info(f"Added skill, marker:\n ```isabelle\n{formal_statement}```\n")      

    def add_new_skill(self, skill_name, description, marker, full_code, origin="", init_update_count=0):
        with self.skill_manager_lock:
            self.sync_checkpoint()

        exists_markers = [value['marker'] for value in self.skills.values()]
        if len(self.encoder.encode(marker)) > 650:
            return
        if len(get_close_matches(marker, exists_markers, n=1, cutoff=0.85)) != 0:
            return

        if not bool(re.match("^[a-zA-Z0-9_']+$", skill_name)):
            skill_name = f"skill_{len(self.skills)}"

        skill_name = skill_name.lower().strip().replace(" ", "_")
        if skill_name in self.skills:
            i = 2
            while f"{skill_name}V{i}" in self.skills:
                i += 1
            skill_name = f"{skill_name}V{i}"

        with self.skill_manager_lock:
            self.sync_checkpoint()

            self.skills[skill_name] = {
                "skill_name": skill_name,
                "marker": marker,
                "description": description,
                "full_code": full_code,
                "origin": origin,
                "update_count": init_update_count,
            }

            # add_text = f"code: {marker}, skill: {skill_name}, description: {description},"
            add_text = marker
            
            # use chroma bridge to add skill to the chromadb
            assert self.chroma_bridge is not None
            data = ("skill_add_text",{
                "skill_name": skill_name,
                "add_text": add_text,
            })
            output = self.chroma_bridge.run_cmd(data)
            if output["error"] is None:
                assert output["output"] == len(
                    self.skills
                ), ("vectordb is not synced with skill.json"
                    f"there are {output['output']} in skilldb but {len(self.skills)} in skills.json")
            
            U.dump_text(
                marker, f"{self.ckpt_dir}/skill/code/{skill_name}.thy"
            )
            U.dump_text(
                description,
                f"{self.ckpt_dir}/skill/description/{skill_name}.txt",
            )
            U.dump_json(self.skills, f"{self.ckpt_dir}/skill/skills.json")
            self.logger.info(f"Added skill, marker:\n ```isabelle\n{marker}```\nfull_code:\nisabelle\n{full_code}\n")

    def update_count(self, skill_name):
        with self.skill_manager_lock:
            self.sync_checkpoint()
            self.skills[skill_name]["update_count"] += 1
            U.dump_json(self.skills, f"{self.ckpt_dir}/skill/skills.json")
    
    def update_count_request(self, request_name):
        with self.skill_manager_lock:
            self.sync_checkpoint()
            self.skill_requests[request_name]["update_count"] += 1
            U.dump_json(self.skill_requests, f"{self.ckpt_dir}/skill/skill_request.json")

    def retrieve_skills(self, query, k):
        ret_skill = []
        k = min(len(self.skills), k)
        if k != 0:
            self.logger.info(f"Skill Manager retrieving for {k} skills")
            with self.skill_manager_lock:
                # query = f"informal statement: {context['informal_statement']}, informal proof: {context['informal_proof']}, formal_statement: {context['formal_statement']}"
                data = ("skill_query", {"query": query, "k": k})
                outputs = self.chroma_bridge.run_cmd(data)
                ret_skill_name = []
                if outputs["error"] is None:
                    ret_skill_name = outputs["output"]
                self.sync_checkpoint()
            self.logger.info(
                f"Skill Manager retrieved skills for query:\n ```\n"
                f"{query}\n```\n"
                f"{', '.join(ret_skill_name)}"
            )

            for skill_name in ret_skill_name:
                retrieved_skill = {
                    "skill": skill_name,
                    "description": self.skills[skill_name]["description"],
                    "code": self.skills[skill_name]["full_code"],
                    "marker": self.skills[skill_name]["marker"],
                }
                ret_skill.append(retrieved_skill)
        return ret_skill

    def retrieve_skills_with_context(self, context):
        ret_skill = []

        k = min(len(self.skills), 6)
        if k != 0:
            self.logger.info(f"Skill Manager retrieving for {k} skills")
            with self.skill_manager_lock:
                query = context['formal_statement']
                data = ("skill_query", {"query": query, "k": k})
                outputs = self.chroma_bridge.run_cmd(data)
                ret_skill_name = []
                if outputs["error"] is None:
                    ret_skill_name = outputs["output"]
                self.sync_checkpoint()
            self.logger.info(
                f"Skill Manager retrieved skills for query:\n ```\n"
                f"{query}\n```\n"
                f"{', '.join(ret_skill_name)}"
            )
        
            for skill_name in ret_skill_name:
                retrieved_skill = {
                    "skill": skill_name,
                    "description": self.skills[skill_name]["description"],
                    "code": self.skills[skill_name]["full_code"],
                    "marker": self.skills[skill_name]["marker"],
                }
                ret_skill.append(retrieved_skill)

        return ret_skill
