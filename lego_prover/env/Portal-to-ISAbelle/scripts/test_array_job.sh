#!/bin/bash
#! Name of the job:
#SBATCH -J cpujob
#! Which project should be charged:
#SBATCH -A JAMNIK-SL3-CPU
#! How many whole nodes should be allocated?
#SBATCH --nodes=1
#! How many (MPI) tasks will there be in total? (<= nodes*32)
#! The skylake/skylake-himem nodes have 32 CPUs (cores) each.
#SBATCH --ntasks=1
#! How much wallclock time will be required?
#SBATCH --time=01:00:00
#! What types of email messages do you wish to receive?
#SBATCH --mail-type=NONE
#! Uncomment this to prevent the job from being requeued (e.g. if
#! interrupted by node failure or system downtime):
##SBATCH --no-requeue
#SBATCH -p skylake
#SBATCH --array=0-9%5

list=(
    "bash scripts/extract_with_hammer_bashes/script_0.sh"
    "bash scripts/extract_with_hammer_bashes/script_1.sh"
    "bash scripts/extract_with_hammer_bashes/script_2.sh"
    "bash scripts/extract_with_hammer_bashes/script_3.sh"
    "bash scripts/extract_with_hammer_bashes/script_4.sh"
    "bash scripts/extract_with_hammer_bashes/script_5.sh"
    "bash scripts/extract_with_hammer_bashes/script_6.sh"
    "bash scripts/extract_with_hammer_bashes/script_7.sh"
    "bash scripts/extract_with_hammer_bashes/script_8.sh"
    "bash scripts/extract_with_hammer_bashes/script_9.sh"
)

${list[SLURM_ARRAY_TASK_ID]}