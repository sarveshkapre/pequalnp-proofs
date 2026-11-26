"""Tabulate wire roles and the synthesis gadgets. Lean checks the literal
clauses against the original encoder's DIMACS output as well as every role."""
from pathlib import Path
root = Path(__file__).resolve().parent
dest = root / "checkout/lean/PEqualNP/Quadrangle"
roles = [".empty"]
rules = []
def wire(role, *args):
    roles.append("." + role + " " + " ".join(map(str,args)))
    return len(roles) - 1
def both(z, x, y):
    rules.append(f".both {z} {x} {y}")
    return z
def union(t, e, gates):
    rows = [wire("row",t,e,i) for i in range(5)]
    cols = [wire("col",t,e,j) for j in range(6)]
    sels = [wire("sel",t,e,k) for k in range(t)]
    values = []
    for i in range(5):
        for j in range(6):
            terms = [rows[i],cols[j]]
            for k,old in enumerate(gates):
                terms.append(both(wire("hit",t,e,k,i,j),sels[k],old[6*i+j]))
            z = wire("side",t,e,i,j)
            rules.append(f".anyOf {z} [" + ",".join(map(str,terms)) + "]")
            values.append(z)
    return values
gates = []
for t in range(3):
    a = union(t,0,gates)
    b = union(t,1,gates)
    gates.append([both(wire("wire",t,i,j),a[6*i+j],b[6*i+j]) for i in range(5) for j in range(6)])
out = union(3,0,gates)
for i,row in enumerate([49,42,22,13,3]):
    for j in range(6):
        rules.append(f".requireBit {out[6*i+j]} " + ("true" if row & (1<<j) else "false"))
assert len(roles) == 657
def chunks(v, n): return [v[i:i+n] for i in range(0,len(v),n)]
s = """import PEqualNP.Quadrangle.Gadgets
import PEqualNP.Quadrangle.Formula

namespace PEqualNP.Quadrangle.Encoding
open PEqualNP.Library.LRAT
set_option maxRecDepth 100000
set_option maxHeartbeats 0
"""
for n,ch in enumerate(chunks(roles,40)):
    s += f"def roles{n} : List Role := [\n" + ",\n".join(ch) + "]\n"
s += "def table : Array Role := [" + ",".join(f"roles{n}" for n in range(len(chunks(roles,40)))) + "].flatten.toArray\n"
s += "def lookup (n : Nat) : Role := table[n]?.getD .empty\n"
for n,ch in enumerate(chunks(rules,30)):
    s += f"def rules{n} : List Rule := [\n" + ",\n".join(ch) + "]\n"
s += "def rules : List Rule := [" + ",".join(f"rules{n}" for n in range(len(chunks(rules,30)))) + "].flatten\n"
s += """
theorem valid : rules.all (Rule.wellFormed lookup) = true := by decide +kernel
theorem formula_eq : Certificate.formula = rules.flatMap Rule.clauses := by decide +kernel

theorem represents_satisfies (h : QuadrangleHandoff.Represents 3 QuadrangleHandoff.graph) :
    FormulaSat Certificate.formula := by
  obtain ⟨I,A,B,S,earlier,gate,output,correct⟩ := h
  let m : Model := ⟨I,A,B,S,earlier,gate,output,correct⟩
  refine ⟨assignment m lookup, ?_⟩
  rw [formula_eq]
  intro c hc
  obtain ⟨g,hg,hc⟩ := List.mem_flatMap.mp hc
  exact rule_sound m lookup g (List.all_eq_true.mp valid g hg) c hc

end PEqualNP.Quadrangle.Encoding
"""
(dest/"Encoding.lean").write_text(s)
print(f"{len(roles)-1} DIMACS variable meanings; {len(rules)} semantic checks")
