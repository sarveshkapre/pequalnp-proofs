import PEqualNP.ThreeGateGain.FiniteFrame

namespace GainFinite

/-- Counts ones in a nine-bit block. The literal table is checked below. -/
def count9 (n : Nat) : Nat :=
  (19255054270729893008491005534149248252256602926781282732690012290033276866808550227997693622604181043369877307314662111123331664736047184874077759948250443227256975055791411108947596559321109802036954624006373818143946017559684403162578529602068048730946422771823999999239149825717005481632390412975320206440279958629013623038381969796702446623878923952740084796477918444418310443408990755144638227854376788458924235859745937832180260096754594561627738988715237553750525742696058226208231293151672720457407743312923599856247524705366024968272077418776390695019160354360691986468851967610039890687248939048398439391504 >>> (4*n)) % 16

def fastSize (m : Nat) : Nat :=
  count9 (m % 2^9) + count9 ((m >>> 9) % 2^9) + count9 ((m >>> 18) % 2^9)

private theorem count9_checked :
    ∀ n : Fin 512, count9 n.val = ((List.finRange 9).filter (fun i => n.val.testBit i.val)).length := by
  decide +kernel

private theorem block_count (m off : Nat) :
    count9 ((m >>> off) % 2^9) =
      ((List.finRange 9).filter (fun i => m.testBit (off+i.val))).length := by
  let x : Fin 512 := ⟨(m >>> off) % 2^9, Nat.mod_lt _ (by decide)⟩
  rw [show count9 ((m >>> off) % 2^9) = _ from count9_checked x]
  congr 1
  apply List.filter_congr
  intro i _
  simp only [x,Nat.testBit_mod_two_pow,i.isLt,decide_true,Bool.true_and,Nat.testBit_shiftRight]

private def first (i : Fin 9) : WordType := ⟨i.val, by omega⟩
private def second (i : Fin 9) : WordType := ⟨9+i.val, by omega⟩
private def third (i : Fin 9) : WordType := ⟨18+i.val, by omega⟩

private theorem split27 : List.finRange 27 =
    (List.finRange 9).map first ++ (List.finRange 9).map second ++ (List.finRange 9).map third := by
  decide +kernel

theorem fastSize_eq (m : Nat) : fastSize m = size27 m := by
  rw [fastSize, size27, positions, split27]
  simp only [List.filter_append,List.length_append,List.filter_map,List.length_map,Function.comp_def,
    first,second,third]
  have low := block_count m 0
  simp only [Nat.shiftRight_zero,Nat.zero_add] at low
  rw [low,block_count,block_count]

end GainFinite
