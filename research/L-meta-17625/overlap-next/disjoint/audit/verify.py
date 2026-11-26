"""Rebuild the finite CNFs and replay the archived RUP hints or satisfying models."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from zipfile import ZipFile

from encode import Model

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def empty_clause(initial, certificate):
    db = {i: frozenset(row) for i, row in enumerate(initial, 1)}
    for line in certificate.decode("ascii").splitlines():
        words = line.split()
        require(words[-1] == "0", "unterminated proof line")
        if words[1] == "d":
            for key in map(int, words[2:-1]):
                del db[key]
            continue
        key = int(words[0])
        end = words.index("0", 1)
        clause = frozenset(map(int, words[1:end]))
        assigned = {-lit for lit in clause}
        require(key not in db, "repeated active clause identifier")
        conflict = any(-lit in assigned for lit in assigned)
        for hint in map(int, words[end + 1:-1]):
            if conflict:
                break
            old = db[hint]
            require(not old & assigned, "propagation hint is already satisfied")
            undecided = [lit for lit in old if -lit not in assigned]
            if not undecided:
                conflict = True
                break
            require(len(undecided) == 1, "hint is not a unit clause")
            assigned.add(undecided[0])
        require(conflict, "proof step derived no contradiction")
        if not clause:
            return
        db[key] = clause
    raise ValueError("certificate did not derive the empty clause")


def main():
    manifest = {}
    for line in (HERE / "sha256.txt").read_text().splitlines()[1:]:
        stem, cnf_hash, cert_hash = line.split()
        manifest[stem] = cnf_hash, cert_hash
    orders = ["".join("A" if i in indices else "O" for i in range(4))
              for indices in combinations(range(4), 2)]
    proved = controls = 0
    with ZipFile(HERE / "certificates.zip") as archive:
        for mode in ("outside", "inside", "cross"):
            for order in [*orders, "OAAOO"]:
                stem = f"{mode}-{order}"
                cnf = Model(order, mode).cnf
                data = cnf.dimacs().encode("ascii")
                control = len(order) == 5
                cert = archive.read(stem + (".model" if control else ".lrat"))
                hashes = tuple(sha256(x).hexdigest() for x in (data, cert))
                require(hashes == manifest[stem], stem + " digest mismatch")
                if control:
                    assignment = set(map(int, cert.split()))
                    require(all(-i not in assignment or i not in assignment
                                for i in range(1, cnf.last + 1)), "inconsistent model")
                    require(all(assignment.intersection(row) for row in cnf.clauses),
                            "control has an unsatisfied clause")
                    controls += 1
                else:
                    empty_clause(cnf.clauses, cert)
                    proved += 1
    print(f"{proved} contradictions replayed and {controls} larger satisfying assignments checked.")


if __name__ == "__main__":
    main()
