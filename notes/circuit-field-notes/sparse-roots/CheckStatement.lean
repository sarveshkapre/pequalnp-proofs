import EightPositiveRoots

example (f g : Polynomial ℝ) (hf : f.support.card ≤ 3) (hg : g.support.card ≤ 3)
    (h : 1 + f * g ≠ 0) :
    (((1 + f * g).roots.toFinset).filter (fun x => 0 < x)).card ≤ 8 :=
  GapAudit.positive_root_count f g hf hg h

#print axioms GapAudit.positive_root_count
