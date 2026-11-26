from pathlib import Path
import re
import subprocess
import sys
import time

from sweep import HERE, TOOLS, digest


def solve_and_replay(folder, seconds):
    cnf = folder / "input.cnf"
    proof = folder / "proof.lrat"
    start = time.monotonic()
    with (folder / "solver.txt").open("w") as out:
        process = subprocess.run([TOOLS / "cadical", "-q", "-t", str(seconds),
                                  "--lrat", "--no-binary", cnf, proof],
                                 stdout=out, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - start, 2)
    checksum, actions = "", ""
    if process.returncode == 20:
        replay = subprocess.run([TOOLS / "lean", "--run", HERE.parents[1] / "bounds/CheckCover.lean",
                                 cnf, proof], capture_output=True, text=True, check=True)
        (folder / "replay.txt").write_text(replay.stdout)
        match = re.search(r"Verified LRAT for (\d+) clauses and (\d+) actions\.", replay.stdout)
        with cnf.open() as handle:
            count = int(handle.readline().split()[-1])
        if match is None or int(match[1]) != count or int(match[2]) < 1:
            raise ValueError(f"Unexpected replay result in {folder}: {replay.stdout}")
        actions = match[2]
        checksum = digest(proof)
        verdict = "VERIFIED_UNSAT"
    elif process.returncode == 0 and "UNKNOWN" in (folder / "solver.txt").read_text():
        proof.unlink(missing_ok=True)
        verdict = "TIMEOUT"
    elif process.returncode == 10:
        verdict = "PROJECTED_SAT"
    else:
        raise RuntimeError(f"CaDiCaL exited {process.returncode} in {folder}")

    return verdict, elapsed, checksum, actions
