import PathWins
import PathSchedule
import PathSearch

namespace PathConclusion
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PathPhysical

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem path_card {e : Fin 4 → Fin n} (einj : Function.Injective e) :
    (PathGeometry.pathEdges e).card = 3 := by
  classical
  have edgeInj : Function.Injective (fun j : Fin 3 => s(e j.castSucc,e j.succ)) := by
    intro i j eq
    rcases Sym2.eq_iff.mp eq with ⟨a,_⟩ | ⟨a,b⟩
    · exact Fin.ext (congrArg (fun x : Fin 4 => x.val) (einj a))
    · have x := congrArg Fin.val (einj a)
      have y := congrArg Fin.val (einj b)
      simp only [Fin.val_castSucc,Fin.val_succ] at x y
      omega
  rw [PathGeometry.pathEdges,Finset.card_image_of_injective _ edgeInj]
  decide

/-- Amritpal's matching inequality holds whenever the residual edges form a
three-edge path, for graphs of every size and for every admissible matching. -/
theorem path_bound (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C)
    (e : Fin 4 → Fin n) (einj : Function.Injective e) (path : Ustar G C = PathGeometry.pathEdges e)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ v, f v ∉ S ∧ G.Adj v.val (f v)) : GeneralThree.wireBound G C S := by
  classical
  have three : (Ustar G C).card = 3 := path ▸ path_card einj
  have edges : G.edgeFinset.Nonempty := by
    obtain ⟨uv,m⟩ := Finset.card_pos.mp (show 0 < (Ustar G C).card by omega)
    exact ⟨uv,(Finset.mem_sdiff.mp m).1⟩
  by_contra fail
  obtain ⟨ac,_,oc,_⟩ := GeneralThree.remaining G C four edges least top three S f inj partners fail
  obtain ⟨W⟩ := PathGeometry.witness four bip edges least top three S f inj partners fail e einj path
  let j := C.gates.length
  have countA := budget (G := G) (C := C) (e := e) j false
  have countO := budget (G := G) (C := C) (e := e) j true
  have no := PathSearch.no_win (PathSchedule.valid W einj least.1 top j)
    (countA.trans (le_of_eq ac)) (countO.trans (le_of_eq oc))
  exact Bool.false_ne_true (no.symm.trans (PathWins.wins least e einj W))

#print axioms path_bound
end PathConclusion
