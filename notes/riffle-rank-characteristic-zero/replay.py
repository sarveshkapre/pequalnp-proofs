"""Replay the local modules against the pinned original definition on macOS."""
from hashlib import sha256
import json
import os
from pathlib import Path
from shutil import copyfile
import subprocess
import sys
from tempfile import TemporaryDirectory


def replay(repo):
    here = Path(__file__).resolve().parent
    lean = repo / "lean"
    tool = Path.home() / ".elan/toolchains/leanprover--lean4---v4.36.0"
    assert (lean / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.36.0"
    libs = sorted((lean / ".lake/packages").glob("*/.lake/build/lib/lean"))
    assert any((lib / "Mathlib/LinearAlgebra/Lagrange.olean").is_file() for lib in libs)
    original = Path("PEqualNP/Defs/RiffleRank.lean")
    digest = sha256((lean / original).read_bytes()).hexdigest()
    assert digest == "a43edc0c5d5e2fb75251499571cff0738a44ebb4976d1e2c8d4a3e7ebe856d02"
    print(f"Upstream definition SHA-256 {digest}", flush=True)
    with TemporaryDirectory(prefix="riffle-lean-", dir="/private/tmp") as tmp:
        scratch = Path(tmp)
        (scratch / original.parent).mkdir(parents=True)
        copyfile(lean / original, scratch / original)
        modules = [original, Path("PackedRiffle.lean"), Path("PairBound.lean"),
                   Path("Sphere.lean")]
        for path in modules[1:]:
            copyfile(here / path, scratch / path)
        sub = lambda path: "(subpath " + json.dumps(str(path)) + ")"
        allowed = [scratch, tool, *libs, "/System/Library", "/usr/lib", "/usr/share", "/Library/Apple"]
        policy = scratch / "offline.sb"
        policy.write_text('\n'.join([
            '(version 1)', '(deny default)', '(import "dyld-support.sb")',
            '(allow sysctl-read)', '(allow file-read-metadata)', '(allow signal (target self))',
            '(allow process-fork)', '(allow process-exec '+sub(tool/"bin")+')',
            '(allow file-read* (literal "/") (literal "/dev/null") (literal "/dev/random") '
            '(literal "/dev/urandom") '+' '.join(map(sub, allowed))+')',
            '(allow file-map-executable '+sub(tool)+' (subpath "/System/Library") (subpath "/usr/lib"))',
            '(allow file-write* '+sub(scratch)+' (literal "/dev/null"))',
        ]))
        env = dict(HOME=tmp, TMPDIR=tmp, PATH=str(tool/"bin"), LEAN_NUM_THREADS="1",
                   LEAN_PATH=os.pathsep.join(map(str, [scratch, *libs])))
        def run(program, *flags):
            subprocess.run(["/usr/bin/sandbox-exec", "-f", policy, tool/"bin"/program, *flags],
                           env=env, cwd=scratch, check=True)
        run("lean", "--version")
        for path in modules:
            run("lean", "-DwarningAsError=true", "-R", tmp, "-o", path.with_suffix(".olean"), path)
        for path in modules:
            run("leanchecker", "-v", ".".join(path.with_suffix("").parts))
        print(f"All {len(modules)} modules compiled and replayed.", flush=True)


if __name__ == "__main__":
    replay(Path(sys.argv[1]).resolve())
