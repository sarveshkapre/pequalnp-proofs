import PEqualNP.ThreeGateGain.GainUpper
import PEqualNP.ThreeGateGain.GainStatement
import PEqualNP.ThreeGateGain.FiniteVerdicts

/-- The net score of every three-intersection circuit on a finite projective plane. -/
theorem PEqualNP.ThreeGateGain.UpperBound :
∀ (P L : Type) [Fintype P] [Fintype L] [Membership P L] [Configuration.ProjectivePlane P L],
  16 ≤ Configuration.ProjectivePlane.order P L →
  ∀ (w : BitVec 9) (r : P → BitVec 6) (c : L → BitVec 6) (rawP : P → Bool) (rawL : L → Bool),
  (Finset.univ.sum fun p : P => Finset.univ.sum fun l : L =>
    let x := r p ||| c l
    let a := x.getLsbD 0 && x.getLsbD 1
    let b := (x.getLsbD 2 || (w.getLsbD 0 && a)) && (x.getLsbD 3 || (w.getLsbD 1 && a))
    let g := (x.getLsbD 4 || (w.getLsbD 2 && a) || (w.getLsbD 3 && b)) &&
             (x.getLsbD 5 || (w.getLsbD 4 && a) || (w.getLsbD 5 && b))
    let accept := rawP p || rawL l || ((w.getLsbD 6 && a) || (w.getLsbD 7 && b) || (w.getLsbD 8 && g))
    if accept then @ite ℤ (p ∈ l) (Classical.propDecidable _) 1 (-1) else 0) ≤
  10 * (Configuration.ProjectivePlane.order P L : ℤ) - 2
 := by
  intro P L _ _ _ _ hq w r c rawP rawL
  let Q (p:P) (l:L) := rawP p || rawL l || GainFinite.threeValue w (r p ||| c l)
  exact (GainStatement.score_direct (fun (p:P) (l:L) => p ∈ l) Q).symm.le.trans
    (GainUpper.plane GainFinite.all_checked hq w r c rawP rawL)
