from __future__ import annotations
import os

import lego_prover.utils as U
from lego_prover.prompts import load_context
import multiprocessing as mp

import logging

class CurriculumAgent:
    def __init__(
        self,
        logger=None,
        ckpt_dir="ckpt",
        resume=False,
        miniF2F_tasks : mp.Queue = None,
        curriculum_task_type : str = "simple_curriculum",
        curriculum_agent_lock = U.WithEmpty()
    ):
        self.logger=logger
        self.miniF2F_tasks = miniF2F_tasks
        self.curriculum_task_type = curriculum_task_type
        self.curriculum_agent_lock = curriculum_agent_lock
        self.ckpt_dir = ckpt_dir
        U.f_mkdir(f"{ckpt_dir}/curriculum/vectordb")
        if resume:
            self.logger.info(f"Loading Curriculum Agent from {ckpt_dir}/curriculum")
            self.sync_checkpoint()
        else:
            self.completed_tasks = []
            self.failed_tasks = []
    
    def sync_checkpoint(self,):
        if os.path.exists(f"{self.ckpt_dir}/curriculum/completed_tasks.json"):
            self.completed_tasks = U.load_json(f"{self.ckpt_dir}/curriculum/completed_tasks.json")
        if os.path.exists(f"{self.ckpt_dir}/curriculum/failed_tasks.json"):
            self.failed_tasks = U.load_json(f"{self.ckpt_dir}/curriculum/failed_tasks.json")

    @property
    def easy_to_hard_curriculum(self):
        result = []
        for name in os.listdir("data/full_data/valid"):
            path = os.path.join("data/full_data/valid", name)
            context = U.load_json(path)
            result.append((path, len(context["informal_proof"])))
        result = sorted(result, key=lambda x: x[1])
        result = [x[0] for x in result]
        return result

    @property
    def progress(self):
        return len(self.completed_tasks)

    def propose_next_task(self, max_retries=5, idx=None):
        if self.curriculum_task_type == "example":
            filename = os.listdir("data/examples")[self.progress]
            task = filename[:-5]
            context = load_context(problem_name=os.path.join("data/examples", filename))
            return task, context
        elif self.curriculum_task_type == "simple_curriculum":
            assert idx is not None
            file_path = self.easy_to_hard_curriculum[idx]
            task = file_path
            context = load_context(file_path)
            return task, context
        elif self.curriculum_task_type == "queue_curriculum":
            while True:
                if self.miniF2F_tasks.qsize() == 0:
                    return "", None
                file_path = self.miniF2F_tasks.get()
                context = load_context(file_path)
                if file_path not in self.completed_tasks:
                    break
            return file_path, context
        else:
            raise NotImplementedError

    def get_task_retry_count(self, task):
        cnt = 0
        for t in self.failed_tasks:
            if t == task:
                cnt += 1
        return cnt

    def propose_next_manual_task(self):
        confirmed = False
        task = ""
        while not confirmed:
            task = input("Enter task: ")
            print(f"Task: {task}")
            confirmed = input("Confirm? (y/n)").lower() in ["y", ""]
        context = load_context(task)
        return task, context

    def update_exploration_progress(self, info):
        with self.curriculum_agent_lock:
            self.sync_checkpoint()

            task = info["task"]
            if info["success"]:
                self.logger.info(f"Completed task {task}.")
                self.completed_tasks.append(task)
            else:
                self.logger.info(
                    f"Failed to complete task {task}. Skipping to next task."
                )
                self.failed_tasks.append(task)

            # clean up tasks and dump to disk
            self.clean_up_tasks()

    def clean_up_tasks(self):
        updated_completed_tasks = []
        # record repeated failed tasks
        updated_failed_tasks = self.failed_tasks
        # dedup but keep order
        for task in self.completed_tasks:
            if task not in updated_completed_tasks:
                updated_completed_tasks.append(task)

        # remove completed tasks from failed tasks
        for task in updated_completed_tasks:
            while task in updated_failed_tasks:
                updated_failed_tasks.remove(task)

        self.completed_tasks = updated_completed_tasks
        self.failed_tasks = updated_failed_tasks

        # dump to json
        U.dump_json(
            self.completed_tasks, f"{self.ckpt_dir}/curriculum/completed_tasks.json"
        )
        U.dump_json(self.failed_tasks, f"{self.ckpt_dir}/curriculum/failed_tasks.json")
