import json
import os
import time
import re
import warnings
from typing import List

import psutil
import subprocess
import logging
import threading

import lego_prover.utils as U


class SubprocessMonitor:
    def __init__(
        self,
        commands: List[str],
        name: str,
        ready_match: str = r".*",
        log_path: str = "logs",
        callback_match: str = r"^(?!x)x$",  # regex that will never match
        callback: callable = None,
        finished_callback: callable = None,
        cwd: str = os.path.expanduser("~"),
        server_port: int = -1,
    ):
        self.commands = commands
        self.server_port = server_port
        start_time = time.strftime("%Y%m%d_%H%M%S")
        self.name = name
        if name == "isabelle_server":
            os.makedirs(f'logs/{name}/{start_time}_logs', exist_ok=True)
            self.logger = logging.getLogger(f'{name}-{server_port}')
            handler = logging.FileHandler(f"logs/{name}/{start_time}_logs/rank_{server_port}.log")
        else:
            self.logger = logging.getLogger(name)
            handler = logging.FileHandler(U.f_join(log_path, f"{start_time}.log"))
        formatter = logging.Formatter(
            "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
        )
        handler.setFormatter(formatter)
        self.logger.addHandler(handler)
        self.logger.setLevel(logging.INFO)
        self.process = None
        self.ready_match = ready_match
        self.ready_event = None
        self.ready_line = None
        self.callback_match = callback_match
        self.callback = callback
        self.finished_callback = finished_callback
        self.thread = None
        self.cwd = cwd

    def _start(self):
        self.logger.info(f"Starting subprocess with commands: {self.commands}")

        self.process = psutil.Popen(
            self.commands,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            stdin=subprocess.PIPE,
            universal_newlines=True,
            cwd=self.cwd
        )
        print(f"Subprocess {self.name} started with PID {self.process.pid}.")
        for line in iter(self.process.stdout.readline, ""):
            self.logger.info(line.strip())
            if re.search(self.ready_match, line):
                self.ready_line = line
                self.logger.info("Subprocess is ready.")
                self.ready_event.set()
                if "chroma" in self.name:
                    break
            if re.search(self.callback_match, line):
                self.callback()
        if not self.ready_event.is_set():
            self.ready_event.set()
            warnings.warn(f"Subprocess {self.name} failed to start.")
        if self.finished_callback:
            self.finished_callback()

    def run(self):
        self.ready_event = threading.Event()
        self.ready_line = None
        self.thread = threading.Thread(target=self._start)
        self.thread.start()
        self.ready_event.wait()

    def stop(self):
        self.logger.info("Stopping subprocess.")
        if self.process and self.process.is_running():
            self.process.terminate()
            self.process.wait()
    
    def terminate(self):
        parent = psutil.Process(self.process.pid)
        for child in parent.children(recursive=True):  # or parent.children() for recursive=False
            child.kill()
        parent.kill()

    def run_action(self, inputs):
        self.logger.info(f"Input: {inputs}")
        self.process.stdin.write(inputs + '\n')
        self.process.stdin.flush()

        for line in iter(self.process.stdout.readline, ""):
            self.logger.info(line)
            if line.startswith('{"error'):
                return json.loads(line)

    @property
    def is_running(self):
        if self.process is None:
            return False
        return self.process.is_running()
