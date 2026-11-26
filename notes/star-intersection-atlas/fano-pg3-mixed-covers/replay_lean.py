"""Build the proof sources against an existing pinned Mathlib and check the targets."""
from graphlib import TopologicalSorter
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import re
import shutil
import subprocess


def main():
    source = Path(__file__).resolve().parent / "lean"
    modules = {p.stem: p for p in source.glob("*.lean")}
    dependencies = {}
    for n, path in modules.items():
        imports = re.findall(r"^import\s+(\S+)", path.read_text(), re.MULTILINE)
        if any(i not in modules and i != "Mathlib.Tactic" for i in imports):
            raise ValueError(f"Unexpected import in {n}")
        dependencies[n] = [i for i in imports if i in modules]
    libraries = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
    version = subprocess.check_output(["lean", "--version"], text=True)
    if "version 4.36.0," not in version:
        raise RuntimeError(version)
    with TemporaryDirectory(prefix="plane-fusion-") as temp:
        directory = Path(temp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([temp, *libraries]))
        for n in TopologicalSorter(dependencies).static_order():
            shutil.copyfile(modules[n], directory / (n + ".lean"))
            subprocess.run(["lean", "-R", temp, "-o", n + ".olean", n + ".lean"],
                           cwd=temp, env=env, check=True)
        for n in ["FusionFanoLower", "FusionRowMixedCounterexample", "FanoMixedFour", "MixedFive"]:
            subprocess.run(["leanchecker", "-v", n], cwd=temp, env=env, check=True)


if __name__ == "__main__":
    main()
