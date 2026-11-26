import PEqualNP.Defs

namespace PEqualNP.Outside.TwinReduction_aux
open PEqualNP.MetaComplexity
abbrev F (n : Nat) := DMFormula n

def pos {n} (f : F n) := DMFormula.rec (motive := fun _ => Prop)
  (fun _ b => b = true) (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f

noncomputable def reads {n} (f : F n) (i : Fin n) := DMFormula.rec (motive := fun _ => Nat)
  (fun j _ => if j = i then 1 else 0) (fun _ _ l r => l + r) (fun _ _ l r => l + r) f

theorem total {n} (f : F n) : (∑ i, reads f i) = f.leaves := by
  induction f with
  | lit => simp [reads, DMFormula.leaves]
  | and _ _ hl hr | or _ _ hl hr =>
    simpa [reads, DMFormula.leaves, Finset.sum_add_distrib] using congrArg₂ Nat.add hl hr

variable {n m : Nat} (p : Fin m → Fin n)
def liftInput (s : Fin n → Fin m) (x : Fin n → Bool) (j : Fin m) :=
  if s (p j) = j then x (p j) else false

-- An optional tree represents a restriction. The missing tree is constant false.
def evalO (f : Option (F n)) (x : Fin n → Bool) := (f.map (·.eval x)).getD false
noncomputable def readO (f : Option (F n)) (i : Fin n) := (f.map (fun g => reads g i)).getD 0
def posO (f : Option (F n)) : Prop := ∀ g ∈ f, pos g

def mergeO (b : Bool) : Option (F n) → Option (F n) → Option (F n)
  | some l, some r => some (if b then .or l r else .and l r)
  | none, r => if b then r else none
  | l, none => if b then l else none

theorem merge_eval b (l r : Option (F n)) x : evalO (mergeO b l r) x =
    (if b then (evalO l x || evalO r x) else (evalO l x && evalO r x)) := by
  cases b <;> cases l <;> cases r <;> simp [evalO,mergeO,DMFormula.eval]

theorem merge_reads b (l r : Option (F n)) i :
    readO (mergeO b l r) i ≤ readO l i + readO r i := by
  cases b <;> cases l <;> cases r <;> simp [readO,mergeO,reads]

theorem merge_pos b (l r : Option (F n)) (hl : posO l) (hr : posO r) :
    posO (mergeO b l r) := by
  cases b <;> cases l <;> cases r <;> simp_all [posO,mergeO,pos]

def restrictF (s : Fin n → Fin m) : F m → Option (F n)
  | .lit j _ => if s (p j) = j then some (.lit (p j) true) else none
  | .and l r => mergeO false (restrictF s l) (restrictF s r)
  | .or l r => mergeO true (restrictF s l) (restrictF s r)

theorem restrict_eval (s : Fin n → Fin m) (f : F m) (hp : pos f) (x : Fin n → Bool) :
    evalO (restrictF p s f) x = f.eval (liftInput p s x) := by
  induction f with
  | lit j b => change b = true at hp; subst b; by_cases h : s (p j) = j <;> simp [restrictF,h,evalO,DMFormula.eval,liftInput]
  | and _ _ hl hr | or _ _ hl hr =>
    simp [restrictF,merge_eval,DMFormula.eval, hl hp.1, hr hp.2]

theorem restrict_pos (s : Fin n → Fin m) (f : F m) : posO (restrictF p s f) := by
  induction f with
  | lit j _ => by_cases h : s (p j) = j <;> simp [restrictF,h,posO,pos]
  | and _ _ hl hr | or _ _ hl hr => exact merge_pos _ _ _ hl hr

theorem restrict_reads (s : Fin n → Fin m) (f : F m) (i : Fin n) :
    readO (restrictF p s f) i ≤ reads f (s i) := by
  induction f with
  | lit j _ =>
    by_cases h : s (p j) = j
    · by_cases t : p j = i
      · rw [t] at h; simp [restrictF,t,h,reads,readO]
      · simp [restrictF,h,readO,reads,t]
    · simp [restrictF,h,readO]
  | and _ _ hl hr | or _ _ hl hr =>
    exact (merge_reads _ _ _ i).trans (Nat.add_le_add hl hr)

def fiber (i : Fin n) := Finset.univ.filter (fun j => p j = i)

theorem cheapest (onto : Function.Surjective p) (g : F m) :
    ∃ s : Fin n → Fin m, (∀ i, p (s i) = i) ∧ ∀ j, reads g (s (p j)) ≤ reads g j := by
  classical
  have ex (i : Fin n) : ∃ j ∈ fiber p i, ∀ k ∈ fiber p i, reads g j ≤ reads g k := by
    obtain ⟨j, hj⟩ := onto i
    exact Finset.exists_min_image _ _ ⟨j, by simp [fiber,hj]⟩
  choose s hs hmin using ex
  exact ⟨s, fun i => by simpa [fiber] using hs i, fun j => hmin _ _ (by simp [fiber])⟩

-- Replace a leaf by the OR of one occurrence of each of its copies.
def bundle (j : Fin m) : List (Fin m) → F m
  | [] => .lit j true
  | k :: ks => .or (.lit k true) (bundle j ks)

theorem bundle_pos j (ks : List (Fin m)) : pos (bundle j ks) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => exact ⟨rfl, ih⟩

theorem bundle_eval j (ks : List (Fin m)) x :
    (bundle j ks).eval x = true ↔ ∃ k ∈ j :: ks, x k = true := by
  induction ks with
  | nil => simp [bundle,DMFormula.eval]
  | cons k ks ih => simp [bundle, DMFormula.eval, ih, or_left_comm]

theorem bundle_reads j (ks : List (Fin m)) i :
    reads (bundle j ks) i = (j :: ks).count i := by
  induction ks with
  | nil => by_cases e : j = i <;> simp_all [bundle,reads]
  | cons k ks ih => simp_all [bundle,reads,List.count_cons,beq_iff_eq,Nat.add_comm,Nat.add_left_comm]

theorem bundle_for (onto : Function.Surjective p) (i : Fin n) :
    ∃ f : F m, pos f ∧ (∀ j, reads f j = if p j = i then 1 else 0) ∧
      ∀ (s : Fin n → Fin m), (∀ a, p (s a) = a) → ∀ x, f.eval (liftInput p s x) = x i := by
  classical
  obtain ⟨j0,h0⟩ := onto i
  have mem (j : Fin m) : j ∈ (fiber p i).toList ↔ p j = i := by simp [fiber]
  cases eq : (fiber p i).toList with
  | nil => simpa [eq] using (mem j0).mpr h0
  | cons j ks =>
    refine ⟨bundle j ks,bundle_pos _ _,?_,?_⟩
    · intro t
      rw [bundle_reads,← eq]
      by_cases h : p t = i
      · simpa [h] using List.count_eq_one_of_mem (Finset.nodup_toList _) ((mem t).mpr h)
      · simpa [h] using List.count_eq_zero.mpr (mt (mem t).mp h)
    · intro s hs x
      apply Bool.eq_iff_iff.mpr
      rw [bundle_eval,← eq]
      constructor
      · rintro ⟨k,hk,v⟩
        have pk := (mem k).mp hk
        by_cases kept : s (p k) = k <;> simp_all [liftInput]
      · intro hv
        exact ⟨s i,(mem _).mpr (hs i),by simp [liftInput,hs,hv]⟩

theorem expand (onto : Function.Surjective p) (f : F n) (hp : pos f) :
    ∃ g : F m, pos g ∧ (∀ j, reads g j = reads f (p j)) ∧
      ∀ s, (∀ i, p (s i) = i) → ∀ x, g.eval (liftInput p s x) = f.eval x := by
  induction f with
  | lit i b =>
    change b = true at hp
    subst b
    obtain ⟨g,hg,v,e⟩ := bundle_for p onto i
    exact ⟨g,hg,fun j => by simpa [reads,eq_comm] using v j,e⟩
  | and l r il ir =>
    obtain ⟨a,ha,ca,ea⟩ := il hp.1
    obtain ⟨b,hb,cb,eb⟩ := ir hp.2
    refine ⟨.and a b,⟨ha,hb⟩,?_,?_⟩
    · intro j; exact congrArg₂ Nat.add (ca j) (cb j)
    · intro s hs x; simp [DMFormula.eval,ea s hs x,eb s hs x]
  | or l r il ir =>
    obtain ⟨a,ha,ca,ea⟩ := il hp.1
    obtain ⟨b,hb,cb,eb⟩ := ir hp.2
    refine ⟨.or a b,⟨ha,hb⟩,?_,?_⟩
    · intro j; exact congrArg₂ Nat.add (ca j) (cb j)
    · intro s hs x; simp [DMFormula.eval,ea s hs x,eb s hs x]


-- Pick one least-used copy per class, restrict all other copies to zero, and
-- simplify. Each old wire is read no more often than ANY copy in its class.
def Fits {n} (X : (Fin n → Bool) → Prop) (H : (Fin n → Bool) → Bool) (f : F n) :=
  ∀ x, X x → f.eval x = H x

def FitsCopies (X : (Fin n → Bool) → Prop) (H : (Fin n → Bool) → Bool) (g : F m) :=
  ∀ s, (∀ i, p (s i) = i) → ∀ x, X x → g.eval (liftInput p s x) = H x

theorem compress (onto : Function.Surjective p) {X H} (live : ∃ x, X x ∧ H x = true)
    (g : F m) (hg : pos g) (ok : FitsCopies p X H g) :
    ∃ f : F n, pos f ∧ Fits X H f ∧ ∀ j, reads f (p j) ≤ reads g j := by
  obtain ⟨s,hs,cheap⟩ := cheapest p onto g
  have val (x) (hx : X x) := (restrict_eval p s g hg x).trans (ok s hs x hx)
  cases eq : restrictF p s g with
  | none =>
    obtain ⟨x,hx,hv⟩ := live
    have hit := val x hx
    simp [eq,evalO,hv] at hit
  | some f =>
    refine ⟨f,restrict_pos p s g f (by simp [eq]),fun x hx => ?_,fun j => ?_⟩
    · simpa [eq,evalO] using val x hx
    · have lower := restrict_reads p s g (p j)
      exact (by simpa [eq,readO] using lower : reads f (p j) ≤ reads g (s (p j))).trans (cheap j)

theorem exactBudget (onto : Function.Surjective p) {X H} (live : ∃ x, X x ∧ H x = true) (k : Nat) :
    (∃ f : F n, pos f ∧ Fits X H f ∧ (∑ j, reads f (p j)) ≤ k) ↔
    ∃ g : F m, pos g ∧ FitsCopies p X H g ∧ g.leaves ≤ k := by
  constructor
  · rintro ⟨f,hf,ok,cost⟩
    obtain ⟨g,hg,counts,evals⟩ := expand p onto f hf
    refine ⟨g,hg,fun s hs x hx => (evals s hs x).trans (ok x hx),?_⟩
    rw [← total,show (∑ j, reads g j) = ∑ j, reads f (p j) from Finset.sum_congr rfl (fun j _ => counts j)]
    exact cost
  · rintro ⟨g,hg,ok,cost⟩
    obtain ⟨f,hf,h,counts⟩ := compress p onto live g hg ok
    refine ⟨f,hf,h,(Finset.sum_le_sum (fun j _ => counts j)).trans ?_⟩
    rwa [total]

theorem exactCaps (onto : Function.Surjective p) {X H} (live : ∃ x, X x ∧ H x = true)
    (B : Fin m → Nat) :
    (∃ f : F n, pos f ∧ Fits X H f ∧ ∀ j, reads f (p j) ≤ B j) ↔
    ∃ g : F m, pos g ∧ FitsCopies p X H g ∧ ∀ j, reads g j ≤ B j := by
  constructor
  · rintro ⟨f,hf,ok,cost⟩
    obtain ⟨g,hg,counts,evals⟩ := expand p onto f hf
    exact ⟨g,hg,fun s hs x hx => (evals s hs x).trans (ok x hx),fun j => (counts j).le.trans (cost j)⟩
  · rintro ⟨g,hg,ok,cost⟩
    obtain ⟨f,hf,h,counts⟩ := compress p onto live g hg ok
    exact ⟨f,hf,h,fun j => (counts j).trans (cost j)⟩

end PEqualNP.Outside.TwinReduction_aux

theorem PEqualNP.Outside.TwinReduction :
  let Pos := fun {d : Nat} (f : PEqualNP.MetaComplexity.DMFormula d) =>
    PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun _ b => b = true)
      (fun _ _ l r => l ∧ r) (fun _ _ l r => l ∧ r) f
  let Reads := fun {d : Nat} (f : PEqualNP.MetaComplexity.DMFormula d) (i : Fin d) =>
    PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Nat) (fun j _ => if j = i then 1 else 0)
      (fun _ _ l r => l + r) (fun _ _ l r => l + r) f
  ∀ (n m : Nat) (p : Fin m → Fin n), Function.Surjective p →
    ∀ (X : (Fin n → Bool) → Prop) (H : (Fin n → Bool) → Bool), (∃ x, X x ∧ H x = true) →
    let Base := fun (f : PEqualNP.MetaComplexity.DMFormula n) => ∀ x, X x → f.eval x = H x
    let Copies := fun (g : PEqualNP.MetaComplexity.DMFormula m) =>
      ∀ (s : Fin n → Fin m), (∀ i, p (s i) = i) → ∀ x, X x →
        g.eval (fun j => if s (p j) = j then x (p j) else false) = H x
    (∀ k : Nat, (∃ f, Pos f ∧ Base f ∧ (∑ j, Reads f (p j)) ≤ k) ↔ ∃ g, Pos g ∧ Copies g ∧ g.leaves ≤ k) ∧
    (∀ B : Fin m → Nat, (∃ f, Pos f ∧ Base f ∧ ∀ j, Reads f (p j) ≤ B j) ↔ ∃ g, Pos g ∧ Copies g ∧ ∀ j, Reads g j ≤ B j) := by
  dsimp only
  intro n m p onto X H live
  exact ⟨TwinReduction_aux.exactBudget p onto live, TwinReduction_aux.exactCaps p onto live⟩
