"""Rebuild the local proofs and run Lean's standalone kernel checker on their conclusions."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile
from graphlib import TopologicalSorter

SOURCE = Path(__file__).resolve().parent
REVISION = "e6bfe1a56efc768d244627b78f175b18de1acd6f"
DEFAULT = ["PlaneDesk", "PlaneBound", "GeneralThree", "ThreeStatesExtremal", "SlackExample", "OneExceptionalOr"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="upstream pequalnp-proofs checkout")
    parser.add_argument("modules", nargs="*", help="optional local theorem modules")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if revision != REVISION:
        parser.error(f"expected {REVISION}, found {revision}")
    sources = {file.stem: file for file in SOURCE.glob("*/*.lean")}
    targets = args.modules or DEFAULT
    if missing := set(targets) - sources.keys():
        parser.error(f"missing local module(s): {sorted(missing)}")
    pending = list(targets)
    dependencies = {}
    external = set()
    while pending:
        module = pending.pop()
        if module in dependencies:
            continue
        imports = set()
        for line in sources[module].read_text().splitlines():
            if line.startswith("import "):
                imports.update(line.split()[1:])
        local = imports & sources.keys()
        external.update(dep for dep in imports - local if dep.startswith("PEqualNP."))
        dependencies[module] = local
        pending.extend(local)
    lean = checkout / "lean"
    subprocess.run(["lake", "build", *("+" + name for name in sorted(external))], cwd=lean, check=True)
    output = subprocess.check_output(["lake", "env", "env", "-0"], cwd=lean)
    environment = dict(os.fsdecode(field).split("=", 1) for field in output.split(b"\0") if field)
    with tempfile.TemporaryDirectory(prefix="overlap-replay-") as dest:
        environment["LEAN_PATH"] = dest + os.pathsep + environment["LEAN_PATH"]
        for module in TopologicalSorter(dependencies).static_order():
            file = sources[module]
            print(f"Building {file.relative_to(SOURCE)}", flush=True)
            subprocess.run(["lean", "-DwarningAsError=true", "-R", file.parent, "-o",
                            Path(dest) / (module + ".olean"), file], cwd=lean, env=environment, check=True)
        for module in targets:
            subprocess.run(["leanchecker", "-v", module], cwd=lean, env=environment, check=True)
        print(f"Verified {', '.join(targets)} at upstream {revision}.", flush=True)


if __name__ == "__main__":
    main()
