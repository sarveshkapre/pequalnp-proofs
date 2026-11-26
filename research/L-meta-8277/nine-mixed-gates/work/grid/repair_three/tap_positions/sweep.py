import hashlib
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = Path(os.environ.get("LEAN_BIN_DIR", Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0/bin"))


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()
