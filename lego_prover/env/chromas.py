
import json
import os
import lego_prover.utils as U
from .process_monitor import SubprocessMonitor
import time


class ChromaBridge:
    def __init__(
        self,
        ckpt_path="ckpt",
        resume=False,
        request_timeout=600,
        log_path="./logs",
    ):
        self.ckpt_path = ckpt_path
        self.resume = "True" if resume else "False"
        self.request_timeout = request_timeout
        self.log_path = log_path
        self.chroma_server = self.get_chroma_process()
        self.chroma_server.run()
        
        # wait for isabelle server to run
        time.sleep(3)

    def get_chroma_process(self):
        U.f_mkdir(self.log_path, "chromadb")
        return SubprocessMonitor(
            commands=[
                "python",
                "chroma_worker.py",
                "--ckpt_path",
                self.ckpt_path,
                "--resume",
                self.resume
            ],
            name="chroma_worker",
            ready_match=r"Chroma worker is ready.",
            log_path=U.f_join(self.log_path, "chromadb"),
            cwd=os.path.abspath("lego_prover/env/")
        )

    def run_cmd(self, cmd):
        cmd = json.dumps(cmd)
        return self.chroma_server.run_action(cmd)