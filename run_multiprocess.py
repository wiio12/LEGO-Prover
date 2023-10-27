import argparse
import logging
import multiprocessing as mp
import os
import pytz
import shutil
from datetime import datetime

from lego_prover.env.chromas import ChromaBridge
from lego_prover.evolver import Evolver
from lego_prover.prover import Prover
import lego_prover.utils as U
from openai_key import *

parser = argparse.ArgumentParser(description='LEGO-Prover')
parser.add_argument('--resume', action='store_true',
                    help='whether to resume from the checkpoint')
parser.add_argument('--data_split', type=str, choices=['valid', 'test'], 
                    default='valid', help='data split to use in the miniF2F dataset')
parser.add_argument('--ckpt_dir', type=str, default='checkpoints/lego_prover_valid_2023_10_27',
                    help='path to the checkpoint directory')
parser.add_argument('--isabelle_path', type=str, default='/data2/wanghaiming/Isabelle2022/',
                    help='path to the Isabelle2022 directory')
parser.add_argument('--model_name', type=str, choices=["gpt-3.5-turbo", "gpt-4"], 
                    default='gpt-3.5-turbo', help='OpenAI model name')
parser.add_argument('--temperature', type=float, default=0.7,
                    help='temperature for sampling the LLM')
parser.add_argument('--num_prover', type=int, default=3,
                    help='number of prover processes')
parser.add_argument('--num_evolver', type=int, default=8,
                    help='number of evolver processes')
parser.add_argument('--num_attempts', type=int, default=100,
                    help='number of proving attempts for each problem in the dataset')

args = parser.parse_args()

resume = args.resume
data_split = args.data_split
ckpt_dir = args.ckpt_dir
isabelle_path = args.isabelle_path
model_name = args.model_name
temperature = args.temperature
number_of_prover_processes = args.num_prover
number_of_evolver_processes = args.num_evolver
number_of_prover_attempts = args.num_attempts

if os.path.exists(ckpt_dir) and not resume:
    text = input(f"the checkpoint directory {ckpt_dir} is already exist, and" + \
                 f"you are not resuming from it, do you want to delete it? (y/n)")
    if "y" in text.lower():
        shutil.rmtree(ckpt_dir, ignore_errors=True)
        resume = False
    else:
        resume = True

# load miniF2F tasks and resume from the checkpoint
miniF2F_tasks = mp.Queue()
problem_names = []
if resume:
    if os.path.exists(f"{ckpt_dir}/curriculum/completed_tasks.json"):
        completed_tasks = U.load_json(
            f"{ckpt_dir}/curriculum/completed_tasks.json")
    if os.path.exists(f"{ckpt_dir}/curriculum/failed_tasks.json"):
        failed_tasks = U.load_json(f"{ckpt_dir}/curriculum/failed_tasks.json")
    print("Current progress: ", len(completed_tasks) + len(set(failed_tasks)))
else:
    completed_tasks = []
    failed_tasks = []
for name in os.listdir(f"data/full_data/{data_split}"):
    path = os.path.join(f"data/full_data/{data_split}", name)
    context = U.load_json(path)
    problem_names.append((path, len(context["informal_proof"])))
problem_names = sorted(problem_names, key=lambda x: x[1])
problem_names = [pn[0] for pn in problem_names]
problem_names = problem_names * number_of_prover_attempts     # 10 * 20 = 200 sketch
for pn in problem_names:
    if pn in completed_tasks:
        continue
    if pn in failed_tasks:
        failed_tasks.remove(pn)
        continue
    miniF2F_tasks.put(pn)
print(f"Sketch to finish: {miniF2F_tasks.qsize()}")

# setup multiprocessing logger
start_time = datetime.now(pytz.timezone(
    'Asia/Shanghai')).strftime("%Y%m%d_%H%M%S")

os.makedirs(f'logs/prover/{start_time}_logs', exist_ok=True)
for rank in range(number_of_prover_processes):
    logger = logging.getLogger(f'prover-{rank}')
    handler = logging.FileHandler(
        f"logs/prover/{start_time}_logs/rank_{rank}.log")
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)

os.makedirs(f'logs/evolver/{start_time}_logs', exist_ok=True)
for evolver_rank in range(number_of_evolver_processes):
    evolver_rank += number_of_prover_processes
    logger = logging.getLogger(f'evolver-{evolver_rank}')
    handler = logging.FileHandler(
        f"logs/evolver/{start_time}_logs/rank_{evolver_rank}.log")
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)

# define the function to run the prover and evolver
def run_prover(rank, tasks, skill_manager_lock, curriculum_agent_lock, chroma_bridge):
    server_port = 8051 + rank

    prover = Prover(
        rank=rank,
        isabelle_path=isabelle_path,
        server_port=server_port,
        model_name=model_name,
        skill_manager_lock=skill_manager_lock,
        action_agent_task_max_retries=1,
        curriculum_task_type="queue_curriculum",
        curriculum_agent_lock=curriculum_agent_lock,
        resume=resume,
        temperature=temperature,
        miniF2F_tasks=tasks,
        ckpt_dir=ckpt_dir,
        chroma_bridge=chroma_bridge,
    )
    prover.learn()

def run_evolver(rank, skill_manager_lock, chroma_bridge):
    server_port = 8011 + rank
    evolver = Evolver(
        rank=rank,
        isabelle_path=isabelle_path,
        ckpt_dir=ckpt_dir,
        server_port=server_port,
        data_split=data_split,
        skill_manager_lock=skill_manager_lock,
        model_name=model_name,
        temperature=temperature,
        chroma_bridge=chroma_bridge
    )
    evolver.evolve()

processes = []
skill_manager_lock = mp.Lock()
curriculum_agent_lock = mp.Lock()
chroma_bridge = ChromaBridge(ckpt_path=ckpt_dir, resume=resume)


# creating processes
for rank in range(number_of_prover_processes):
    p = mp.Process(target=run_prover, args=(rank, miniF2F_tasks,
                   skill_manager_lock, curriculum_agent_lock, chroma_bridge))
    processes.append(p)
    p.start()

for rank in range(number_of_evolver_processes):
    rank += number_of_prover_processes
    p = mp.Process(target=run_evolver, args=(
        rank, skill_manager_lock, chroma_bridge))
    processes.append(p)
    p.start()

# completing process
for p in processes:
    p.join()
