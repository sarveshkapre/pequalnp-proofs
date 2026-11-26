import PEqualNP.FiveRows.Partition
import PEqualNP.Atlas56.Cover

/-! A short certificate for the capacity of the shared shape. Every selection
of five row profiles lies in one of 126 lists. Each list, even using all its
rows at once, separates at most 22 classes of column assignments. -/
namespace FiveRowPartition
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def rowType : Fin 26 → Block := ![0x0, 0xa0a0a0a000000000, 0xaa000000aa000000, 0xaa00aa0000000000, 0xaa00aa00aa000000, 0xaaa0aaa000000000, 0xc0c0c0c000000000, 0xcc000000cc000000, 0xcc00cc0000000000, 0xcc00cc00cc000000, 0xccc0ccc000000000, 0xe0e0e0e000000000, 0xee000000ee000000, 0xee00ee0000000000, 0xee00ee00ee000000, 0xeee0eee000000000, 0xf0f00000f0f00000, 0xf0f0a0a0f0f00000, 0xf0f0c0c0f0f00000, 0xf0f0e0e0f0f00000, 0xfaf00000faf00000, 0xfaf0aaa0faf00000, 0xfcf00000fcf00000, 0xfcf0ccc0fcf00000, 0xfef00000fef00000, 0xfef0eee0fef00000]
private def rowIndex : Code → Fin 26 := fun r => (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 16, 16, 0, 2, 7, 12, 16, 20, 22, 24, 0, 0, 0, 0, 0, 1, 6, 11, 0, 3, 8, 13, 0, 5, 10, 15, 0, 0, 0, 0, 16, 17, 18, 19, 0, 4, 9, 14, 16, 21, 23, 25] : Fin 64 → Fin 26) r.toFin
private def mask : Fin 126 → Nat := ![0x33ff87f, 0x220ffff, 0x3c0f7bf, 0x3ff8c7f, 0x3ff52bf, 0x23f4d57, 0x33bf93f, 0x2aeef7b, 0x3ff8fe3, 0x3ff18d7, 0x3cfffc3, 0x37bf8bf, 0x37373bf, 0x3f09ce7, 0x23fad7f, 0x2b3633f, 0x3ff57d5, 0x3ddffc5, 0x2ae5ad7, 0x37393a7, 0x2cf4aeb, 0x330f7fd, 0x3cdffc9, 0x22aeffb, 0x330fbbf, 0x30ffd6b, 0x3d577dd, 0x3d594dd, 0x359fb9d, 0x2cfafeb, 0x2e567d9, 0x3f0f7bd, 0x1df1fc7, 0x3c0ad7f, 0x3f05ad7, 0x28c73bf, 0x2ae9ce7, 0x28cef7f, 0x37ff83f, 0x17f18ff, 0x330afeb, 0x280ffff, 0x3309c7f, 0x230ed7f, 0x2bf4a57, 0x2e30493, 0x28c1cd7, 0x33094bf, 0x2aee8bb, 0x3ff213f, 0x2a3e73b, 0x230e73f, 0x333943f, 0x370a87f, 0x2b0ad7f, 0x330f7ab, 0x3ff23ab, 0x22ef93f, 0x2a0f3bf, 0x3f0f783, 0x22a77dd, 0x22a4a7f, 0x222f3bf, 0x2b50265, 0x3c01ae7, 0x3f0f07d, 0x3f394a7, 0x2b1e73d, 0x222e73f, 0x23b4a3f, 0x2aeef45, 0x3ff255d, 0x22e70bf, 0x2a273bf, 0x370f93f, 0x3ff27c9, 0x28effc9, 0x3d0ffc9, 0x34bfbab, 0x3ddafc9, 0x260ebbb, 0x37babab, 0x3cf77c9, 0x224f57d, 0x31dfd5d, 0x23fed5d, 0x2a0f93f, 0x2af4a7b, 0x2c04afb, 0x3f194bd, 0x28c8cfb, 0x22afd7f, 0x2afef59, 0x3c0ffdd, 0x28c5b97, 0x284f3bd, 0x3dd1cd5, 0x37ba93f, 0x3ddad5d, 0x310ffdd, 0x3ff5a97, 0x233e33f, 0x263e3bb, 0x373f39d, 0x295e75d, 0x3d5f39d, 0x2aef83f, 0x3c09d67, 0x2c0ed7b, 0x3cf1ae3, 0x3f1f7a9, 0x28cffeb, 0x33f713f, 0x3cf73ab, 0x20affeb, 0x3ff9c67, 0x233e53f, 0x2cfed6b, 0x23fed6b, 0x3f0f83f, 0x2a473bd, 0x2aeffc1, 0x2e0ad7b, 0x3f0ffc1, 0x33ffd49, 0x3dfffc1]
private def compatible : Fin 26 → Nat := ![0x3fffffffffffffffffffffffffffffff, 0x4ffbc724dc347356fffffff239cffff, 0x1990fbfea7807fff67adeff9d2ffa7f, 0x15f7d7eebfffffba77ff8feafff0d8df, 0x59117fffff907ba767ffeeedda5daff, 0x5fffc628fcb473fe7ff8ffaa3b8f9df, 0x3e6cb90d3dbcb8c3b0605fb76ef767ab, 0x2b06e2d9e707fb055d81e39dfdff3f16, 0x3f77dbeef87ffed85fce0b2bf7ebd5e6, 0x2b06e3f8f187fa79fd8c132df5ff9596, 0x3e7cd90d3e3cb8dc18dcef33eee365ae, 0x3eecbc1f7df3f46122615ff733d66feb, 0x3b8fee99ea5c77075e90c6dd9f6f3e57, 0x3ff7d7eeb87fffda5fef0b6af7e2dcc7, 0x3bf7d7f8f9fd777a7e8d1a6cd7f79cf7, 0x3efcdfeebe7bf45e4efd8f72bbea6dcf, 0x307b63f712b6c8ac811630c17e5bdf79, 0x327f24f218a65bf4731730d1229ddff9, 0x336ba715d4bc99c0830350f96e5747b9, 0x326fa4175cb6d9e0330350f932d74ff9, 0x38d943bf0232acae89fa9dc59d2bfb79, 0x1fd944f21aeb0ffeffffbdd4c1adfbfb, 0x2caa7ad72307ec87092220c7fc5b3f1c, 0x2faaff15f7c4bacf8d47723fec57a79c, 0x388b6a9f2216ec8709b285c79f6b3f5d, 0x3fffffffffffffffffffff7effffffff]
private def rowIndices := List.finRange 26
private def tests (k : Fin 126) : List Block :=
  (rowIndices.filter (fun i => (mask k).testBit i.val)).map rowType
private def entry (i : Fin 26) : Atlas56.Entry := ⟨i.castLE (by decide),compatible i,0⟩
private def allOptions : Nat := 2^126-1

private theorem lookup : ∀ r : Code, profile r = rowType (rowIndex r) := by decide +kernel
private theorem transpose : ∀ (i : Fin 26) (k : Fin 126),
    (compatible i).testBit k.val = (mask k).testBit i.val := by decide +kernel
private theorem small : ∀ k : Fin 126, ((tests k).foldl split [-1]).length ≤ 22 := by decide +kernel
private theorem covered : Atlas56.check 5 (rowIndices.map entry) allOptions 0 = true := by decide +kernel

private theorem dead (xs : List Atlas56.Entry) : Atlas56.finishE 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons h t ih => simpa [Atlas56.finishE] using ih

theorem shared_columns {n : Nat} (rows : Fin 5 → Code) (cols : Fin n → Code)
    (sep : ∀ i j, (∀ r, shared (rows r &&& cols i) = shared (rows r &&& cols j)) → i = j) :
    n ≤ 22 := by
  classical
  let needed := Finset.univ.image (fun r => rowIndex (rows r))
  let used := rowIndices.filter (fun t => t ∈ needed)
  have huniv (t : Fin 26) : t ∈ rowIndices := List.mem_finRange _
  have same : used.toFinset = needed := by ext t; simp [used,huniv]
  have unique : rowIndices.Nodup := List.nodup_finRange _
  have le : used.length ≤ 5 := by
    rw [← List.toFinset_card_of_nodup (unique.filter _),same]
    exact Finset.card_image_le.trans (by simp)
  have accept := Atlas56.check_sound (rowIndices.map entry) 5 allOptions 0 (used.map entry)
    ((List.filter_sublist (l := rowIndices)).map entry) (by simpa using le) covered
  have good := accept.resolve_right (fun he => he.2 (dead _))
  obtain ⟨k,hk⟩ := Nat.exists_testBit_of_ne_zero good
  obtain ⟨bound,allowed⟩ := (Atlas56.fold_bits _ Atlas56.Entry.ok allOptions k hk)
  have lt : k < 126 := by
    by_contra! high
    have hh : allOptions < 2^k := lt_of_lt_of_le (by decide : allOptions < 2^126)
      (Nat.pow_le_pow_right (by decide) high)
    simp [Nat.testBit_lt_two_pow hh] at bound
  let index : Fin 126 := ⟨k,lt⟩
  apply distinct_bound (tests index) cols _ (small index)
  intro i j eq
  apply sep i j
  intro r
  rw [← profile_correct,← profile_correct,lookup]
  apply eq
  let t := rowIndex (rows r)
  have included : t ∈ used := List.mem_toFinset.mp (by rw [same]; exact Finset.mem_image.mpr ⟨r,by simp,rfl⟩)
  have hh := allowed (entry t) (List.mem_map_of_mem included)
  have b : (mask index).testBit t.val = true := (transpose t index).symm.trans hh
  exact List.mem_map.mpr ⟨t,List.mem_filter.mpr ⟨huniv t,b⟩,rfl⟩
end FiveRowPartition
