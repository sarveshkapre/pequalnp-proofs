import MatchOrders

namespace MatchProjected.Controls
private def base (a : Raw) : Selector := ⟨a,0,false,0⟩
private def earlier (i : Fin 4) : Selector := ⟨0,0,true,i⟩
private def operations : Fin 4 → Bool := ![false,false,true,true]
private def l : Fin 4 → Selector := ![base 5,base 2,earlier 0,earlier 1]
private def r : Fin 4 → Selector := ![base 40,base 16,base 0,base 0]
private def tops : Fin 3 → TopSel := ![⟨0,8,4,0⟩,⟨0,16,8,0⟩,⟨4,0,0,4⟩]

/-- The four-gate order really does fit the full six-variable graph truth table if
the common-neighbour restriction on ordinary raw supports is removed. All six
top masks and every other gate port are legal. -/
theorem ordinary_support_matters :
    graphOK 1 = true ∧ allowed 1 (l 0).raw = false ∧ allowed 1 (r 0).raw = false ∧
    (∀ i : Fin 3, allowed 1 (tops i).leaf && leafOK 1 (tops i).center (tops i).leaf = true) ∧
    (∀ i : Fin 4, i ≠ 0 → portOK 1 (l i) = true ∧ portOK 1 (r i) = true) ∧
    (∀ v : Raw, let wires := schedule operations l r
      (topVal (tops 0) wires v || topVal (tops 1) wires v || topVal (tops 2) wires v) =
        !(independent 1 v)) := by decide

private def literal (a : Raw) : Wire := ⟨a,true,hit a⟩

private def guardedPair (v a b : Raw) : Bool :=
  let p := gate false (literal a) (literal b)
  let h := gate true p (literal 0)
  side 0 1 ![h,zero,zero,zero] v && side b 0 (fun _ => zero) v

/-- Three dirty ANDs and three promotion ORs suffice in the projected window.
The three raw-empty masks here represent globally nonempty outside literals. -/
theorem extra_pair_passes :
    ∀ v : Raw, (guardedPair v 1 8 || guardedPair v 2 16 || guardedPair v 4 32) =
      !(independent 0 v) := by decide

#print axioms ordinary_support_matters
#print axioms extra_pair_passes
end MatchProjected.Controls
