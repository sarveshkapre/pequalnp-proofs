import Mathlib

namespace SparseProductRoots
open Real Set
open scoped BigOperators

def HasZeros (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ t : Fin n → ℝ, StrictMono t ∧ ∀ i, f (t i) = 0

/-- An exponentially rescaled derivative loses at most one distinct real zero. -/
theorem rolle_step {n : ℕ} {f g : ℝ → ℝ} (m : ℝ) (roots : HasZeros (n+1) f)
    (diff : ∀ x, HasDerivAt (fun t => exp (-m*t) * f t) (exp (-m*x) * g x) x) :
    HasZeros n g := by
  obtain ⟨t, ht, zero⟩ := roots
  have interval (i : Fin n) : ∃ z ∈ Ioo (t i.castSucc) (t i.succ), g z = 0 := by
    obtain ⟨z,hz,ez⟩ := exists_hasDerivAt_eq_zero (ht i.castSucc_lt_succ)
      (fun x _ => (diff x).continuousAt.continuousWithinAt)
      (by simp only [zero,mul_zero]) (fun x _ => diff x)
    exact ⟨z,hz,(mul_eq_zero.mp ez).resolve_left (exp_pos _).ne'⟩
  choose z hz ez using interval
  refine ⟨z, ?_, ez⟩
  intro i j hij
  have le : i.succ ≤ j.castSucc := by
    change i.val+1 ≤ j.val
    exact hij
  exact (hz i).2.trans_le ((ht.monotone le).trans (hz j).1.le)

noncomputable def eval {ι : Type*} [Fintype ι] (w c : ι → ℝ) (t : ℝ) :=
  ∑ i, c i * exp (w i * t)

theorem remove_exponent {ι : Type*} [Fintype ι] {n : ℕ} (w c : ι → ℝ) (m : ℝ)
    (h : HasZeros (n+1) (eval w c)) : HasZeros n (eval w (fun i => c i * (w i-m))) := by
  apply rolle_step m h
  intro x
  have split (t : ℝ) : exp (-m*t) * eval w c t = ∑ i, c i * exp ((w i-m)*t) := by
    unfold eval
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (w i-m)*t = -m*t+w i*t by ring, exp_add]
    ring
  simp_rw [split]
  have term (i : ι) : HasDerivAt (fun t => c i * exp ((w i-m)*t))
      (c i * (exp ((w i-m)*x) * (w i-m))) x := by
    simpa using ((((hasDerivAt_id x).const_mul (w i-m)).exp).const_mul (c i))
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => term i) using 1
  unfold eval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (w i-m)*x = -m*x+w i*x by ring, exp_add]
  ring

/-- Apply any list of exponential eliminations. Its entries need not be consecutive. -/
theorem remove_many {ι : Type*} [Fintype ι] {n : ℕ} (w c : ι → ℝ) (ms : List ℝ)
    (h : HasZeros (n+ms.length) (eval w c)) :
    HasZeros n (eval w (fun i => c i * (ms.map (fun m => w i-m)).prod)) := by
  induction ms generalizing c with
  | nil => simpa using h
  | cons m ms ih =>
    have h' : HasZeros ((n+ms.length)+1) (eval w c) := by simpa [Nat.add_assoc] using h
    have step := ih (fun i => c i*(w i-m)) (remove_exponent w c m h')
    simpa [mul_assoc] using step

/-- At two distinct zeros of an alternating three-term exponential sum, its middle
log-weight is strictly above the interpolated endpoint log-weights. -/
theorem two_zeros_strict {p q low mid high t₀ t₁ : ℝ} (hp : 0 < p) (hq : 0 < q)
    (distinct : t₀ ≠ t₁)
    (first : q * exp (low-p*t₀) + p * exp (high+q*t₀) = (p+q)*exp mid)
    (second : q * exp (low-p*t₁) + p * exp (high+q*t₁) = (p+q)*exp mid) :
    q*low+p*high < (p+q)*mid := by
  have one {t : ℝ} (ne : low-p*t ≠ high+q*t)
      (root : q * exp (low-p*t) + p * exp (high+q*t) = (p+q)*exp mid) :
      q*low+p*high < (p+q)*mid := by
    have pos : 0 < p+q := by positivity
    have sum : q/(p+q) + p/(p+q) = 1 := by field_simp; ring
    have strict := strictConvexOn_exp.2 (mem_univ (low-p*t)) (mem_univ (high+q*t)) ne
      (div_pos hq pos) (div_pos hp pos) sum
    simp only [smul_eq_mul] at strict
    have avg : q/(p+q)*(low-p*t) + p/(p+q)*(high+q*t) = (q*low+p*high)/(p+q) := by ring
    have val : q/(p+q)*exp (low-p*t) + p/(p+q)*exp (high+q*t) = exp mid := by
      field_simp
      linarith
    rw [avg,val,exp_lt_exp] at strict
    linarith [(div_lt_iff₀ pos).mp strict]
  by_cases eq : low-p*t₀ = high+q*t₀
  · apply one (t := t₁) _ second
    intro eq'
    apply distinct
    have prod : (p+q)*(t₀-t₁) = 0 := by nlinarith [eq,eq']
    rcases mul_eq_zero.mp prod with no | no
    · linarith
    · linarith
  · exact one eq first

#print axioms remove_many
#print axioms two_zeros_strict
end SparseProductRoots

open Real Set
namespace EightRootAudit
theorem minorant {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    1+h*x/(1+x) ≤ (1+x)^h := by
  have hp : 0 < 1+x := by linarith
  have e := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at e
  have row : x/(1+x) = 1-(1+x)⁻¹ := by field_simp; ring
  have hlog : x/(1+x) ≤ Real.log (1+x) := by linarith
  rw [Real.rpow_def_of_pos hp]
  nlinarith [mul_le_mul_of_nonneg_left hlog hh, Real.add_one_le_exp (Real.log (1+x)*h),
    show h*(x/(1+x)) = h*x/(1+x) by ring]

theorem threshold {z a d e p q r t L k : ℝ}
    (hz : 0 < z) (hz' : z < 1) (ha : 0 < a) (hd : 0 < d)
    (hp : 0 < p) (hr : 0 < r) (ht : 0 < t) (hL : 0 < L)
    (window : 0 ≤ d-(1-z)*a*(p/r)/L-z*e*(q/t))
    (hcoef : (t/z)*(r*L/((1-z)*(t/z)))^(1-z) < k) :
    0 < t/z-e*q/d ∧ (t/z)*((a*p/d)/(t/z-e*q/d))^(1-z) < k := by
  let T := t/z
  let C := r*L/((1-z)*T)
  have hT : 0 < T := div_pos ht hz
  have hz1 : 0 < 1-z := by linarith
  have hC : 0 < C := div_pos (mul_pos hr hL) (mul_pos hz1 hT)
  have hP : 0 < a*p/d := by positivity
  have iden : (C*(T-e*q/d)-a*p/d)*((1-z)*d/(r*L)) =
      d-(1-z)*a*(p/r)/L-z*e*(q/t) := by
    dsimp [C,T]
    field_simp
    ring
  have multpos : 0 < (1-z)*d/(r*L) := by positivity
  have row : a*p/d ≤ C*(T-e*q/d) := by
    rw [← iden] at window
    have := nonneg_of_mul_nonneg_left window multpos
    linarith
  have hdiff : 0 < T-e*q/d := pos_of_mul_pos_right (hP.trans_le row) hC.le
  have ratio := (div_le_iff₀ hdiff).mpr row
  exact ⟨hdiff, lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_pos hP hdiff).le ratio hz1.le) hT.le) hcoef⟩

theorem wronskian {u v P Q T k : ℝ} (hu : 0 < u) (huv : u<v)
    (hp : 0<P) (hqt : Q<T) (ht : 0<T)
    (hk : T*(P/(T-Q))^(1-u/v)<k) (x : ℝ) :
    0 < k*(u*P*exp ((u-v)*x)+(v-u)*(T-Q)*exp (u*x))-v*P*T := by
  have hv : 0<v := hu.trans huv
  have hb : 0<T-Q := sub_pos.mpr hqt
  have hR : 0<P/(T-Q) := div_pos hp hb
  let c := log (P/(T-Q))/v
  have hc : exp (v*c) = P/(T-Q) := by
    dsimp [c]
    rw [show v*(log (P/(T-Q))/v)=log (P/(T-Q)) by field_simp, exp_log hR]
  have pc : P=(T-Q)*exp (v*c) := by rw [hc]; field_simp
  have rt : (P/(T-Q))^(1-u/v) = exp ((v-u)*c) := by
    rw [rpow_def_of_pos hR];congr 1;dsimp [c];field_simp
  rw [rt] at hk
  have kpos : 0 < k := (mul_pos ht (exp_pos _)).trans hk
  have kup : P*T < k*((T-Q)*exp (u*c)) := by
    have step := mul_lt_mul_of_pos_right hk (mul_pos hb (exp_pos (u*c)))
    calc
      P*T = T*exp ((v-u)*c)*((T-Q)*exp (u*c)) := by
        rw [pc]
        rw [show T*exp ((v-u)*c)*((T-Q)*exp (u*c)) =
          T*(T-Q)*(exp ((v-u)*c)*exp (u*c)) by ring, ← exp_add]
        rw [show (v-u)*c+u*c=v*c by ring];ring
      _ < _ := step
  have sum : v ≤ u*exp ((u-v)*(x-c))+(v-u)*exp (u*(x-c)) := by
    nlinarith [mul_le_mul_of_nonneg_left (add_one_le_exp ((u-v)*(x-c))) hu.le,
      mul_le_mul_of_nonneg_left (add_one_le_exp (u*(x-c))) (sub_nonneg.mpr huv.le)]
  have iden : u*P*exp ((u-v)*x)+(v-u)*(T-Q)*exp (u*x) =
      ((T-Q)*exp (u*c))*(u*exp ((u-v)*(x-c))+(v-u)*exp (u*(x-c))) := by
    conv_lhs => rw [pc]
    have v1 : exp (v*c)*exp ((u-v)*x)=exp (u*c)*exp ((u-v)*(x-c)) := by
      rw [←exp_add,←exp_add];congr 1;ring
    have v2 : exp (u*x)=exp (u*c)*exp (u*(x-c)) := by
      rw [← exp_add];congr 1;ring
    linear_combination u*(T-Q)*v1 + (v-u)*(T-Q)*v2
  rw [iden]
  apply sub_pos.mpr
  calc
    v*P*T = v*(P*T) := by ring
    _ < v*(k*((T-Q)*exp (u*c))) := mul_lt_mul_of_pos_left kup hv
    _ = (k*((T-Q)*exp (u*c)))*v := by ring
    _ ≤ (k*((T-Q)*exp (u*c)))*(u*exp ((u-v)*(x-c))+(v-u)*exp (u*(x-c))) :=
      mul_le_mul_of_nonneg_left sum (mul_pos kpos (mul_pos hb (exp_pos (u*c)))).le
    _ = _ := by ring
#print axioms minorant
#print axioms threshold
#print axioms wronskian

noncomputable def band (P Q k u v x : ℝ) : ℝ := P-k*exp (u*x)+Q*exp (v*x)
noncomputable def slope (Q k u v x : ℝ) : ℝ :=
  -k*(exp (u*x)*u)+Q*(exp (v*x)*v)

theorem band_diff (P Q k u v x : ℝ) :
    HasDerivAt (band P Q k u v) (slope Q k u v x) x := by
  have term (w : ℝ) : HasDerivAt (fun y : ℝ => exp (w*y)) (exp (w*x)*w) x := by
    simpa using (((hasDerivAt_id x).const_mul w).exp)
  unfold band slope
  simpa only [zero_sub,neg_mul] using
    (((hasDerivAt_const x P).fun_sub ((term u).const_mul k)).fun_add ((term v).const_mul Q))

theorem numerator {u v P Q T k : ℝ} (hu : 0 < u) (huv : u<v)
    (hp : 0<P) (hqt : Q<T) (ht : 0<T) (hk : T*(P/(T-Q))^(1-u/v)<k) (x : ℝ) :
    0 < slope Q k u v x * band 0 T k u v x -
        band P Q k u v x * slope T k u v x := by
  have w := wronskian hu huv hp hqt ht hk x
  have iden : slope Q k u v x * band 0 T k u v x - band P Q k u v x * slope T k u v x =
      exp (v*x)*(k*(u*P*exp ((u-v)*x)+(v-u)*(T-Q)*exp (u*x))-v*P*T) := by
    unfold slope band
    rw [show (u-v)*x=u*x-v*x by ring,exp_sub]
    field_simp
    ring
  rw [iden]
  exact mul_pos (exp_pos _) w

/-- There cannot be three distinct ordered real zeros after the fifth Rolle step. -/
theorem no_three {u v P Q T k H a : ℝ} (hu : 0 < u) (huv : u<v)
    (hp : 0<P) (hqt : Q<T) (ht : 0<T) (hk : T*(P/(T-Q))^(1-u/v)<k)
    (hH : 0<H) (ha : 0<a) :
    ¬ ∃ x y z : ℝ, x<y ∧ y<z ∧
      (∀ w ∈ ({x,y,z} : Set ℝ), band P Q k u v w + H*exp (a*w)*band 0 T k u v w=0) := by
  let A := band P Q k u v
  let B := band 0 T k u v
  let G := fun w => A w + H*exp (a*w)*B w
  let f := fun w => A w/B w + H*exp (a*w)
  have hk0 : 0<k := (mul_pos ht (rpow_pos_of_pos (div_pos hp (sub_pos.mpr hqt)) _)).trans hk
  let c := log (k/T)/(v-u)
  have bp (x : ℝ) : B x=0 ↔ x=c := by
    have fac : B x = exp (u*x)*(T*exp ((v-u)*x)-k) := by
      dsimp [B,band]
      rw [show (v-u)*x=v*x-u*x by ring, exp_sub]
      field_simp
      ring
    rw [fac,mul_eq_zero]
    simp only [(exp_pos (u*x)).ne',false_or,sub_eq_zero]
    constructor
    · intro h
      have hh : exp ((v-u)*x)=k/T := (eq_div_iff ht.ne').mpr (by linarith)
      apply (eq_div_iff (sub_ne_zero.mpr huv.ne')).mpr
      rw [← hh,log_exp];ring
    · intro h
      have hvc : (v-u)*x=log (k/T) := by rw [h];dsimp [c];field_simp
      rw [hvc,exp_log (div_pos hk0 ht)];field_simp
  have wc (x : ℝ) := numerator hu huv hp hqt ht hk x
  have gc : G c ≠ 0 := by
    intro ng
    have bc := (bp c).mpr rfl
    have ac : A c = 0 := by simpa [G,bc] using ng
    have w := wc c
    change 0 < _*B c - A c*_ at w
    simp [bc,ac] at w
  have strictly (x : ℝ) (hx : x ≠ c) : HasDerivAt f
      ((slope Q k u v x * B x - A x * slope T k u v x)/(B x)^2 + H*(exp (a*x)*a)) x := by
    have br : B x ≠ 0 := fun h => hx ((bp x).mp h)
    have dA := band_diff P Q k u v x
    have dB := band_diff 0 T k u v x
    have de : HasDerivAt (fun w : ℝ => H*exp (a*w)) (H*(exp (a*x)*a)) x := by
      simpa using ((((hasDerivAt_id x).const_mul a).exp).const_mul H)
    exact (dA.div dB br).add de
  have noPair {x y : ℝ} (hxy : x<y) (hx : G x=0) (hy : G y=0)
      (same : y<c ∨ c<x) : False := by
    have avoid (w : ℝ) (hw : w ∈ Icc x y) : w ≠ c := by
      rcases same with h|h
      · exact (hw.2.trans_lt h).ne
      · exact (h.trans_le hw.1).ne'
    have eq0 {w : ℝ} (hg : G w=0) (hw : w ∈ Icc x y) : f w = 0 := by
      have br : B w ≠ 0 := fun h => avoid w hw ((bp w).mp h)
      dsimp [f];field_simp [br];dsimp [G] at hg;linarith
    obtain ⟨w,hw,hzero⟩ := exists_hasDerivAt_eq_zero hxy
      (fun w hw => (strictly w (avoid w hw)).continuousAt.continuousWithinAt)
      ((eq0 hx ⟨le_rfl,hxy.le⟩).trans (eq0 hy ⟨hxy.le,le_rfl⟩).symm)
      (fun w hw => strictly w (avoid w ⟨hw.1.le,hw.2.le⟩))
    have nb : B w ≠ 0 := fun h => avoid w ⟨hw.1.le,hw.2.le⟩ ((bp w).mp h)
    exact (add_pos (div_pos (wc w) (sq_pos_of_ne_zero nb))
      (mul_pos hH (mul_pos (exp_pos _) ha))).ne' hzero
  rintro ⟨x,y,z,hxy,hyz,roots⟩
  have gx : G x=0 := roots _ (by simp)
  have gy : G y=0 := roots _ (by simp)
  have gz : G z=0 := roots _ (by simp)
  rcases lt_trichotomy y c with h|h|h
  · exact noPair hxy gx gy (Or.inl h)
  · exact gc (h ▸ gy)
  · exact noPair hyz gy gz (Or.inr h)
#print axioms no_three

theorem twice_crossing {z u v alfa beta k x y : ℝ} (hz : 0<z) (hz1 : z<1)
    (huv : z*v=u) (hv : 0<v) (ha : 0<alfa) (hb : 0<beta) (hxy : x≠y)
    (rx : alfa*exp (-u*x)+beta*exp ((v-u)*x)=k)
    (ry : alfa*exp (-u*y)+beta*exp ((v-u)*y)=k) :
    exp ((1-z)*log (alfa/(1-z))+z*log (beta/z))<k := by
  have hz0 : 0<1-z := by linarith
  let l := log (alfa/(1-z))
  let h := log (beta/z)
  have r {w : ℝ} (root : alfa*exp (-u*w)+beta*exp ((v-u)*w)=k)
      (ne : l+(-u)*w ≠ h+(v-u)*w) : exp ((1-z)*l+z*h)<k := by
    have eqw : 1-z+z=1 := by ring
    have stric := strictConvexOn_exp.2 (mem_univ (l+(-u)*w))
      (mem_univ (h+(v-u)*w)) ne hz0 hz eqw
    simp only [smul_eq_mul] at stric
    have eq1 : (1-z)*(l+ -u*w)+z*(h+(v-u)*w)=(1-z)*l+z*h := by
      linear_combination w*huv
    rw [eq1, exp_add l (-u*w),exp_add h ((v-u)*w)] at stric
    dsimp [l,h] at stric ⊢
    rw [exp_log (div_pos ha hz0),exp_log (div_pos hb hz)] at stric
    convert stric using 1
    rw [←root]; field_simp
  by_cases hxx : l+ -u*x=h+(v-u)*x
  · apply r ry
    intro hyy
    have hprod : v*(x-y)=0 := by linear_combination hyy-hxx
    exact hxy (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hv.ne'))
  · exact r rx hxx

theorem two_to_coef {z u v r t k A B L x y : ℝ} (hz : 0<z) (hz1 : z<1)
    (huv : z*v=u) (hv : 0<v) (hr : 0<r) (ht : 0<t) (ha : 0<A)
    (hb : 0<B) (hL : 0<L) (minor : L≤A*B^(z/(1-z))) (hxy : x≠y)
    (rx : (r*A)*exp (-u*x)+(t*B)*exp ((v-u)*x)=k)
    (ry : (r*A)*exp (-u*y)+(t*B)*exp ((v-u)*y)=k) :
    (t/z)*(r*L/((1-z)*(t/z)))^(1-z)<k := by
  have hz0 : 0<1-z := by linarith
  have t0 := div_pos ht hz
  have aux := twice_crossing hz hz1 huv hv (mul_pos hr ha) (mul_pos ht hb) hxy rx ry
  have hm := (Real.log_le_log hL minor)
  rw [Real.log_mul ha.ne' (rpow_pos_of_pos hb _).ne',log_rpow hb] at hm
  have hi := mul_le_mul_of_nonneg_left hm hz0.le
  have divEq : (1-z)*(z/(1-z))=z := by field_simp
  have hsum : (1-z)*log L ≤ (1-z)*log A+z*log B := by
    calc
      _ ≤ (1-z)*(log A+(z/(1-z))*log B) := hi
      _ = _ := by linear_combination log B*divEq
  apply lt_of_le_of_lt _ aux
  rw [rpow_def_of_pos (div_pos (mul_pos hr hL) (mul_pos hz0 t0))]
  nth_rw 1 [← exp_log t0]
  rw [←exp_add]
  apply exp_le_exp.mpr
  simp only [log_div (mul_pos hr hL).ne' (mul_pos hz0 t0).ne',log_mul hr.ne' hL.ne',
    log_mul hz0.ne' t0.ne',log_div ht.ne' hz.ne',
    log_div (mul_pos hr ha).ne' hz0.ne',log_mul hr.ne' ha.ne',
    log_div (mul_pos ht hb).ne' hz.ne',log_mul ht.ne' hb.ne']
  linarith only [hsum]

theorem single_factor {d u v : ℝ} (hd : 0<d) (hu : 0<u) (huv : u<v) :
    (d/(d+u))*(1+u/(d+v)) ≤ (d/(d+u))*((d+v)/(d+u))^(u/(v-u)) := by
  have hdu := add_pos hd hu
  have hvu := sub_pos.mpr huv
  have hv := hu.trans huv
  have hx := div_pos hvu hdu
  have hh := div_pos hu hvu
  apply mul_le_mul_of_nonneg_left _ (div_pos hd hdu).le
  have h := minorant hx hh.le
  have fr : 1+(v-u)/(d+u)=(d+v)/(d+u) := by field_simp;ring
  rw [fr] at h
  convert h using 1
  field_simp
#print axioms twice_crossing
#print axioms two_to_coef
#print axioms single_factor

def es (u v a : ℝ) : Fin 6 → ℝ := ![0,u,v,a,a+u,a+v]
def cs (p q r t k H : ℝ) : Fin 6 → ℝ := ![p,-k,q,-H*r,H*k,-H*t]
def mult3 (e u v : ℝ) := e*(e-u)*(e-v)

theorem six_to_two {u v a p q r t k H : ℝ} (hu : 0 < u) (huv : u < v) (hva : v < a)
    (hH : 0 < H)
    (five : SparseProductRoots.HasZeros 5 (SparseProductRoots.eval (es u v a) (cs p q r t k H))) :
    ∃ x y : ℝ, x≠y ∧
      ∀ w ∈ ({x,y} : Set ℝ),
      (r*(mult3 a u v/mult3 (a+u) u v))*exp (-u*w)+
      (t*(mult3 (a+v) u v/mult3 (a+u) u v))*exp ((v-u)*w)=k := by
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hb : 0 < mult3 (a+u) u v := by
    unfold mult3
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have rem := SparseProductRoots.remove_many (n:=2) (es u v a) (cs p q r t k H) [0,u,v] five
  obtain ⟨w,hw,z⟩ := rem
  have one (i : Fin 2) := z i
  have atIndex (i : Fin 2) : (r*(mult3 a u v/mult3 (a+u) u v))*exp (-u*w i)+
        (t*(mult3 (a+v) u v/mult3 (a+u) u v))*exp ((v-u)*w i)=k := by
    have h0 := one i
    simp [SparseProductRoots.eval,es,cs,Fin.sum_univ_succ] at h0
    have scale : 0  <  H * exp (a*w i) := mul_pos hH (exp_pos _)
    have split (e : ℝ) : exp ((a+e)*w i)=exp (a*w i)*exp (e*w i) := by rw [add_mul,exp_add]
    rw [split u,split v] at h0
    have h1 : r*mult3 a u v -k*mult3 (a+u) u v*exp (u*w i)+
        t*mult3 (a+v) u v*exp (v*w i)=0 := by
      apply (mul_eq_zero.mp (show H*exp (a*w i)*(_)=0 from ?_)).resolve_left scale.ne'
      unfold mult3;linear_combination -h0
    rw [show -u*w i= -(u*w i) by ring,exp_neg,show (v-u)*w i=v*w i-u*w i by ring,exp_sub]
    field_simp
    ring_nf at h1 ⊢
    linear_combination h1
  refine ⟨w 0,w 1,(hw (by decide : (0 : Fin 2) < 1)).ne,?_⟩
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl|rfl
  · exact atIndex 0
  · exact atIndex 1

theorem six_to_four {u v a p q r t k H : ℝ} (hu : 0 < u) (hva : u < a)
    (five : SparseProductRoots.HasZeros 5 (SparseProductRoots.eval (es u v a) (cs p q r t k H))) :
    ∃ x y z : ℝ, x < y ∧ y < z ∧ ∀ w ∈ ({x,y,z} : Set ℝ),
      band (a*p/(a-u)) ((a-v)*q/(a-u)) k u v w +
      (H*u/(a-u))*exp (a*w)* band 0 (v*t/u) k u v w = 0 := by
  obtain ⟨w,hw,zero⟩ := SparseProductRoots.remove_exponent (n:=4) (es u v a) (cs p q r t k H) a five
  have atIndex (i : Fin 4) : band (a*p/(a-u)) ((a-v)*q/(a-u)) k u v (w i)+
       (H*u/(a-u))*exp (a*w i)*band 0 (v*t/u) k u v (w i)=0 := by
    have h := zero i
    simp [SparseProductRoots.eval,es,cs,Fin.sum_univ_succ] at h
    rw [show (a+u)*w i=a*w i+u*w i by ring,exp_add,
      show (a+v)*w i=a*w i+v*w i by ring,exp_add] at h
    unfold band
    field_simp
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨w 0,w 1,w 2,hw (by decide),hw (by decide),?_⟩
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl|rfl|rfl
  · exact atIndex 0
  · exact atIndex 1
  · exact atIndex 2
#print axioms six_to_two
#print axioms six_to_four

noncomputable def lower (d u v : ℝ) := (d/(d+u))*(1+u/(d+v))
noncomputable def low3 (a u v : ℝ) := lower a u v * lower (a-u) u v * lower (a-v) u v

theorem product_minor {u v a : ℝ} (hu : 0 < u) (huv : u < v) (hva : v < a) :
    low3 a u v ≤ (mult3 a u v / mult3 (a+u) u v)*
      (mult3 (a+v) u v / mult3 (a+u) u v)^(u/(v-u)) := by
  have aa : 0 < a := (hu.trans huv).trans hva
  have au := sub_pos.mpr (huv.trans hva)
  have av := sub_pos.mpr hva
  have vp := hu.trans huv
  let b := fun (d : ℝ) => (d+v)/(d+u)
  let w := u/(v-u)
  have bp {d : ℝ} (hd : 0 < d) : 0 < b d := div_pos (add_pos hd vp) (add_pos hd hu)
  have lp {d : ℝ} (hd : 0 < d) : 0 < lower d u v := by unfold lower;positivity
  have h {d : ℝ} (hd : 0 < d) : lower d u v ≤ (d/(d+u))*((b d)^w) :=
    single_factor hd hu huv
  have hprod := mul_le_mul_of_nonneg (mul_le_mul_of_nonneg (h aa) (h au) (lp aa).le ((lp au).le.trans (h au)))
    (h av) (mul_pos (lp aa) (lp au)).le ((lp av).le.trans (h av))
  have ratio : (mult3 (a+v) u v/mult3 (a+u) u v) = b a * b (a-u) * b (a-v) := by
    dsimp [mult3,b]
    rw [show a+u-u=a by ring,show a+v-v=a by ring,show a-u+u=a by ring,
        show a-v+v=a by ring,show a-u+v=a+v-u by ring,show a-v+u=a+u-v by ring]
    field_simp
  have first : mult3 a u v/mult3 (a+u) u v =
      (a/(a+u))*((a-u)/(a-u+u))*((a-v)/(a-v+u)) := by
    dsimp [mult3]
    rw [show a+u-u=a by ring,show a-u+u=a by ring,show a-v+u=a+u-v by ring]
    field_simp
  unfold low3
  apply hprod.trans
  rw [first,ratio,Real.mul_rpow (mul_pos (bp aa) (bp au)).le (bp av).le,
        Real.mul_rpow (bp aa).le (bp au).le]
  dsimp [w]
  exact le_of_eq (by ring)

theorem exclude_five {u v a p q r t k H : ℝ} (hu : 0 < u) (huv : u < v)
    (hva : v < a) (hp : 0 < p) (hr : 0 < r) (ht : 0 < t) (hH : 0 < H)
    (window : 0 ≤ (a-u)-(1-u/v)*a*(p/r)/low3 a u v-(u/v)*(a-v)*(q/t)) :
    ¬ SparseProductRoots.HasZeros 5 (SparseProductRoots.eval (es u v a) (cs p q r t k H)) := by
  intro five
  have vp := hu.trans huv
  have ap := vp.trans hva
  have au := sub_pos.mpr (huv.trans hva)
  have av := sub_pos.mpr hva
  have zpos := div_pos hu vp
  have zlt := (div_lt_one vp).mpr huv
  have zrel : (u/v)*v=u := by field_simp
  have low_pos {d : ℝ} (hd : 0 < d) : 0 < lower d u v := by unfold lower;positivity
  have Lpos : 0 < low3 a u v := mul_pos (mul_pos (low_pos ap) (low_pos au)) (low_pos av)
  have mhigh {e : ℝ} (he : v < e) : 0 < mult3 e u v := by
    unfold mult3
    exact mul_pos (mul_pos (vp.trans he) (sub_pos.mpr (huv.trans he))) (sub_pos.mpr he)
  have ao := mhigh hva
  have am := mhigh (e:=a+u) (by linarith)
  have ab := mhigh (e:=a+v) (by linarith)
  obtain ⟨x,y,hxy,hroot⟩ := six_to_two hu huv hva hH five
  have rho := product_minor hu huv hva
  have zz : (u/v)/(1-u/v)=u/(v-u) := by field_simp
  rw [←zz] at rho
  have hk := two_to_coef zpos zlt zrel vp hr ht (div_pos ao am) (div_pos ab am) Lpos rho hxy
    (hroot x (by simp)) (hroot y (by simp))
  obtain ⟨qs,hs⟩ := threshold zpos zlt ap au hp hr ht Lpos window hk
  have eqT : t/(u/v)=v*t/u := by field_simp
  rw [eqT] at qs hs
  have posT : 0 < v*t/u := by positivity
  apply no_three hu huv (div_pos (mul_pos ap hp) au) (sub_pos.mp qs) posT hs
    (div_pos (mul_pos hH hu) au) ap
  exact six_to_four hu (huv.trans hva) five
#print axioms exclude_five

end EightRootAudit


namespace GapAudit
open Real Set SparseProductRoots
open EightRootAudit

def rectE (w d : ℝ) : Fin 4 → ℝ := ![0,w,d,d+w]
def rectC (A B C D : ℝ) : Fin 4 → ℝ := ![A,-B,C,-D]

theorem edge_log {w d A B C D : ℝ} (hw : 0 < w) (hwd : w < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (roots : HasZeros 3 (eval (rectE w d) (rectC A B C D))) :
    (1-w/d)*log (((d+w)/(d-w))*A)+(w/d)*log C < log B := by
  have hd := hw.trans hwd
  have hu := div_pos hw hd
  have hu' := (div_lt_one hd).mpr hwd
  have hθ : 0 < 1-w/d := by linarith
  have hp : 0 < (d+w)/d*A := mul_pos (div_pos (add_pos hd hw) hd) hA
  have hq : 0 < (w/d)*C := mul_pos hu hC
  obtain ⟨x,inc,z⟩ := remove_exponent (n:=2) _ _ (d+w) roots
  have eqn (i : Fin 2) : ((d+w)/d*A)*exp (-w*x i)+((w/d)*C)*exp ((d-w)*x i)=B := by
    have h := z i
    simp [eval,rectE,rectC,Fin.sum_univ_succ] at h
    rw [show -w*x i= -(w*x i) by ring, exp_neg,show (d-w)*x i=d*x i-w*x i by ring,exp_sub]
    field_simp
    ring_nf at h ⊢
    linear_combination -h
  have key := twice_crossing hu hu' (show w/d*d=w by field_simp) hd hp hq
    (inc (by decide : (0:Fin 2)<1)).ne (eqn 0) (eqn 1)
  have e1 : ((d+w)/d*A)/(1-w/d)=(d+w)/(d-w)*A := by field_simp
  have e2 : (w/d*C)/(w/d)=C := by field_simp
  rw [e1,e2] at key
  exact (Real.lt_log_iff_exp_lt hB).mpr key

theorem reversed {w d A B C D : ℝ}
    (roots : HasZeros 3 (eval (rectE w d) (rectC A B C D))) :
    HasZeros 3 (eval (rectE w d) (rectC D C B A)) := by
  obtain ⟨x,inc,hs⟩ := roots
  refine ⟨fun i => -x (Fin.rev i),?_,?_⟩
  · intro i j h; exact neg_lt_neg (inc (Fin.rev_lt_rev.mpr h))
  · intro i
    have z := hs (Fin.rev i)
    let t := x (Fin.rev i)
    change eval _ _ t=0 at z
    change eval _ _ (-t)=0
    simp [eval,rectE,rectC,Fin.sum_univ_succ] at z ⊢
    simp only [exp_neg,add_mul,exp_add] at z ⊢
    field_simp
    ring_nf at z ⊢
    linear_combination -z

theorem rectangle {w d A B C D : ℝ} (hw : 0 < w) (hwd : w < d)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (roots : HasZeros 3 (eval (rectE w d) (rectC A B C D))) :
    (d+w)^2*A*D < (d-w)^2*B*C := by
  let R := (d+w)/(d-w)
  have hsum := add_pos (hw.trans hwd) hw
  have hdif := sub_pos.mpr hwd
  have hR : 0 < R := div_pos hsum hdif
  have fl := edge_log hw hwd hA hB hC roots
  have gl := edge_log hw hwd hD hC hB (reversed roots)
  change (1-w/d)*log (R*A)+(w/d)*log C < log B at fl
  change (1-w/d)*log (R*D)+(w/d)*log B < log C at gl
  rw [log_mul hR.ne' hA.ne'] at fl
  rw [log_mul hR.ne' hD.ne'] at gl
  have hgap : 0 < 1-w/d := sub_pos.mpr ((div_lt_one (hw.trans hwd)).mpr hwd)
  have cmp : (1-w/d)*(2*log R+log A+log D-log B-log C) < 0 := by
    linear_combination fl+gl
  have less := neg_of_mul_neg_right cmp hgap.le
  have raw : log (R*R*A*D) < log (B*C) := by
    rw [log_mul (by positivity : R*R*A≠0) hD.ne',log_mul (by positivity : R*R≠0) hA.ne',
      log_mul hR.ne' hR.ne',log_mul hB.ne' hC.ne']
    linarith
  have rr := (log_lt_log_iff (by positivity : 0<R*R*A*D) (mul_pos hB hC)).mp raw
  dsimp [R] at rr
  field_simp at rr
  nlinarith only [rr]
#print axioms rectangle

def tenE (s u v a b : ℝ) : Fin 10 → ℝ :=
    ![0,s,s+u,s+v,s+a,s+(a+u),s+(a+v),s+(a+b),s+(a+b+u),s+(a+b+v)]
def tenC (M h j k : ℝ) : Fin 10 → ℝ :=
    ![1,-M,M*k,-M,M*h,-M*h*k,M*h,-M*h*j,M*h*j*k,-M*h*j]
noncomputable def original (s u v a b M h j k x : ℝ) : ℝ :=
    1-M*exp (s*x)*(1-h*exp (a*x)+h*j*exp ((a+b)*x))*(1-k*exp (u*x)+exp (v*x))
theorem ten_eq (s u v a b M h j k x : ℝ) : original s u v a b M h j k x =
    eval (tenE s u v a b) (tenC M h j k) x := by
  simp [original,eval,tenE,tenC,Fin.sum_univ_succ,add_mul,exp_add]
  ring

def weight (s u v a b e : ℝ) := (s+e)*(a+b-e)*(a+b+u-e)*(a+b+v-e)
theorem weight_pos {s u v a b e : ℝ} (hs : 0 < s) (hu : 0 < u) (huv : u < v)
    (hvb : v < b) (he : 0 ≤ e) (he' : e ≤ a+v) : 0  <  weight s u v a b e := by
  unfold weight
  exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)

theorem nine_to_five {s u v a b M h j k : ℝ}
    (hs : 0 < s) (hu : 0 < u) (huv : u < v) (hva : v < a) (hvb : v < b) (hM : 0 < M)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    let W := weight s u v a b
    HasZeros 5 (eval (EightRootAudit.es u v a)
      (EightRootAudit.cs (W 0/W u) (W v/W u) (W a/W (a+u)) (W (a+v)/W (a+u))
          k (h*W (a+u)/W u))) := by
  let W := weight s u v a b
  change HasZeros 5 (eval _ (EightRootAudit.cs (W 0/W u) (W v/W u) (W a/W (a+u))
    (W (a+v)/W (a+u)) k (h*W (a+u)/W u)))
  have eqn : original s u v a b M h j k = eval (tenE s u v a b) (tenC M h j k) :=
    funext (ten_eq s u v a b M h j k)
  rw [eqn] at nine
  let L := [0,s+(a+b),s+(a+b+u),s+(a+b+v)]
  have cf : (fun i => tenC M h j k i*(L.map (fun l => tenE s u v a b i-l)).prod) =
       ![0,M*W 0,-M*k*W u,M*W v,-M*h*W a,M*h*k*W (a+u),-M*h*W (a+v),0,0,0] := by
    funext i
    fin_cases i  <;> simp [tenE,tenC,L,W,weight] <;> ring_nf <;> simp
  have left := remove_many (n:=5) (tenE s u v a b) (tenC M h j k) L nine
  obtain ⟨x,inc,hx⟩ := left
  have wu : 0  <  W u := weight_pos hs hu huv hvb hu.le (by linarith)
  have wau : 0  <  W (a+u) := weight_pos hs hu huv hvb (by linarith) (by linarith)
  refine ⟨x,inc,?_⟩
  intro i
  have eqz := hx i
  rw [cf] at eqz
  have sc := mul_pos (mul_pos hM wu) (exp_pos (s*x i))
  apply (mul_eq_zero.mp (show M*W u*exp (s*x i)*(_)=0 from ?_)).resolve_left sc.ne'
  conv_rhs => rw [←eqz]
  simp [eval,tenE,EightRootAudit.es,EightRootAudit.cs,Fin.sum_univ_succ,add_mul,exp_add]
  field_simp [wu.ne',wau.ne']
#print axioms nine_to_five
def weightH (s u v a e : ℝ) := (s+a+e)*(a+e)*(a+e-u)*(a+e-v)
theorem weightH_pos {s u v a e : ℝ} (hs : 0<s) (hu : 0<u) (huv : u<v) (hva : v<a)
    (he : 0≤e) : 0 < weightH s u v a e := by
  unfold weightH
  exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by linarith)
theorem nine_to_high {s u v a b M h j k : ℝ}
    (hs : 0 < s) (hu : 0 < u) (huv : u < v) (hva : v < a) (hvb : v < b) (hM : 0 < M) (hh : 0 < h)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    let W := weightH s u v a
    HasZeros 5 (eval (EightRootAudit.es u v b)
      (EightRootAudit.cs (W 0/W u) (W v/W u) (W b/W (b+u)) (W (b+v)/W (b+u))
          k (j*W (b+u)/W u))) := by
  let W := weightH s u v a
  change HasZeros 5 (eval _ (EightRootAudit.cs (W 0/W u) (W v/W u) (W b/W (b+u))
    (W (b+v)/W (b+u)) k (j*W (b+u)/W u)))
  have eqn : original s u v a b M h j k = eval (tenE s u v a b) (tenC M h j k) :=
    funext (ten_eq s u v a b M h j k)
  rw [eqn] at nine
  let L := [0,s,s+u,s+v]
  have cf : (fun i => tenC M h j k i*(L.map (fun l => tenE s u v a b i-l)).prod) =
       ![0,0,0,0,M*h*W 0,-M*h*k*W u,M*h*W v,-M*h*j*W b,M*h*j*k*W (b+u),-M*h*j*W (b+v)] := by
    funext i
    fin_cases i  <;> simp [tenE,tenC,L,W,weightH] <;> ring_nf <;> simp
  have left := remove_many (n:=5) (tenE s u v a b) (tenC M h j k) L nine
  obtain ⟨x,inc,hx⟩ := left
  have wu : 0  <  W u := weightH_pos hs hu huv hva hu.le
  have wau : 0  <  W (b+u) := weightH_pos hs hu huv hva (by linarith)
  refine ⟨x,inc,?_⟩
  intro i
  have eqz := hx i
  rw [cf] at eqz
  have sc := mul_pos (mul_pos (mul_pos hM hh) wu) (exp_pos ((s+a)*x i))
  apply (mul_eq_zero.mp (show M*h*W u*exp ((s+a)*x i)*(_)=0 from ?_)).resolve_left sc.ne'
  conv_rhs => rw [←eqz]
  simp [eval,tenE,EightRootAudit.es,EightRootAudit.cs,Fin.sum_univ_succ,add_mul,exp_add]
  field_simp [wu.ne',wau.ne']
#print axioms nine_to_high

theorem six_inner {u v d p q r t k H : ℝ} (hu : 0 < u) (huv : u < v) (hvd : v < d)
    (hq : 0 < q) (ht : 0 < t) (hk : 0 < k) (hH : 0 < H)
    (five : HasZeros 5 (eval (EightRootAudit.es u v d) (EightRootAudit.cs p q r t k H))) :
    (d+(v-u))^2*(d-u)*(d+v)*t < (d-(v-u))^2*(d-v)*(d+u)*q := by
  have hv := hu.trans huv
  have hd := hv.trans hvd
  have ww := sub_pos.mpr huv
  have gap : v-u < d := by linarith
  let A := k*u*(d-u)
  let B := q*v*(d-v)
  let C := H*k*(d+u)*u
  let D := H*t*(d+v)*v
  have hfour : HasZeros 3 (eval (rectE (v-u) d) (rectC A B C D)) := by
    obtain ⟨x,inc,hs⟩ := remove_many (n:=3) (EightRootAudit.es u v d)
      (EightRootAudit.cs p q r t k H) [0,d] five
    refine ⟨x,inc,?_⟩
    intro i
    have h := hs i
    apply (mul_eq_zero.mp (show exp (u*x i)*(_)=0 from ?_)).resolve_left (exp_pos _).ne'
    rw [←h]
    simp [eval,EightRootAudit.es,EightRootAudit.cs,rectE,rectC,A,B,C,D,
      Fin.sum_univ_succ,add_mul,sub_mul,exp_add,exp_sub]
    field_simp
    ring
  have hA : 0 < A := by dsimp [A]; exact mul_pos (mul_pos hk hu) (sub_pos.mpr (huv.trans hvd))
  have hB : 0 < B := by dsimp [B]; exact mul_pos (mul_pos hq hv) (sub_pos.mpr hvd)
  have hC : 0 < C := by dsimp [C];positivity
  have hD : 0 < D := by dsimp [D];positivity
  have h := rectangle ww gap hA hB hC hD hfour
  have sc : 0 < k*u*H*v := by positivity
  apply lt_of_mul_lt_mul_right _ sc.le
  dsimp [A,B,C,D] at h
  linear_combination h
#print axioms six_inner

theorem six_outer {u v d p q r t k H : ℝ} (hu : 0 < u) (huv : u < v) (hvd : v < d)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t) (hH : 0 < H)
    (five : HasZeros 5 (eval (EightRootAudit.es u v d) (EightRootAudit.cs p q r t k H))) :
    (d+v)^2*(d+u)*(d+v-u)*p*t < (d-v)^2*(d+u-v)*(d-u)*q*r := by
  have hv := hu.trans huv
  have hd := hv.trans hvd
  have ww := sub_pos.mpr huv
  let A := p*u*(d+u)
  let B := q*(v-u)*(d+u-v)
  let C := H*r*(d-u)*u
  let D := H*t*(d+v-u)*(v-u)
  have hfour : HasZeros 3 (eval (rectE v d) (rectC A B C D)) := by
    obtain ⟨x,inc,hs⟩ := remove_many (n:=3) (EightRootAudit.es u v d)
      (EightRootAudit.cs p q r t k H) [u,d+u] five
    refine ⟨x,inc,?_⟩
    intro i
    have h := hs i
    rw [←h]
    simp [eval,EightRootAudit.es,EightRootAudit.cs,rectE,rectC,A,B,C,D,Fin.sum_univ_succ,add_mul,exp_add]
    ring
  have hA : 0 < A := by dsimp [A];positivity
  have hB : 0 < B := by dsimp [B];exact mul_pos (mul_pos hq ww) (by linarith)
  have hC : 0 < C := by dsimp [C];exact mul_pos (mul_pos (mul_pos hH hr) (by linarith)) hu
  have hD : 0 < D := by dsimp [D];exact mul_pos (mul_pos (mul_pos hH ht) (by linarith)) ww
  have h := rectangle hv hvd hA hB hC hD hfour
  have sc : 0 < u*H*(v-u) := by positivity
  apply lt_of_mul_lt_mul_right _ sc.le
  dsimp [A,B,C,D] at h
  linear_combination h
#print axioms six_outer

def up (u v d j : ℝ) := (d+j)*(d+j-u)*(d+j-v)
def down (u v d j : ℝ) := (d-j)*(d+u-j)*(d+v-j)
def midNum (u v a b j : ℝ) := up u v a j * down u v b j
def topNum (u v a b j : ℝ) := up u v (a+b) j * up u v b j

theorem offset {s x y d A B : ℝ} (hs : 0 ≤ s) (hx : 0<x) (hxy : x<y)
    (hd : 0<d) (hA : 0≤A)
    (h : (s+x)*(s+y+d)*A < (s+y)*(s+x+d)*B) :
    x*(y+d)*A < y*(x+d)*B := by
  have posY := hx.trans hxy
  have py := mul_pos posY (add_pos hx hd)
  have pf : 0 < (s+y)*(s+x+d) := by positivity
  have cmp : x*(y+d)*((s+y)*(s+x+d)) ≤ y*(x+d)*((s+x)*(s+y+d)) := by
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hd.le (sub_nonneg.mpr hxy.le)) hs)
      (show 0 ≤ s+x+y+d by positivity)]
  apply lt_of_mul_lt_mul_right _ pf.le
  calc
    x*(y+d)*A*((s+y)*(s+x+d)) = (x*(y+d)*((s+y)*(s+x+d)))*A := by ring
    _ ≤ (y*(x+d)*((s+x)*(s+y+d)))*A := mul_le_mul_of_nonneg_right cmp hA
    _ = ((s+x)*(s+y+d)*A)*(y*(x+d)) := by ring
    _ < ((s+y)*(s+x+d)*B)*(y*(x+d)) := mul_lt_mul_of_pos_right h py
    _ = _ := by ring

theorem tests {s u v a b M h j k : ℝ} (hs : 0 < s) (hu : 0 < u) (huv : u < v)
    (hva : v < a) (hvb : v < b) (hM : 0 < M) (hh : 0 < h) (hj : 0 < j) (hk : 0 < k)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    let W := weight s u v a b
    (up u v a v * down u v a u)*(W u*W (a+v)) <
       (up u v a u * down u v a v)*(W v*W (a+u)) ∧
    (a-u) - (1-u/v)*a*((W 0/W u)/(W a/W (a+u)))/EightRootAudit.low3 a u v -
       (u/v)*(a-v)*((W v/W u)/(W (a+v)/W (a+u))) < 0 ∧
    ((a+u)*midNum u v a b u)*((a+b+v)*topNum u v a b v) <
       ((a+v)*midNum u v a b v)*((a+b+u)*topNum u v a b u) := by
  let W := weight s u v a b
  let V := weightH s u v a
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hb := hv.trans hvb
  have au := sub_pos.mpr (huv.trans hva)
  have bU := sub_pos.mpr (huv.trans hvb)
  have bV := sub_pos.mpr hvb
  have w (e : ℝ) (h0 : 0≤e) (h1 : e≤a+v) : 0 < W e := weight_pos hs hu huv hvb h0 h1
  have whi (e : ℝ) (he : 0≤e) : 0 < V e := weightH_pos hs hu huv hva he
  have w0 := w 0 le_rfl (by linarith)
  have wu := w u hu.le (by linarith)
  have wv := w v hv.le (by linarith)
  have wa := w a ha.le (by linarith)
  have wA := w (a+u) (by positivity) (by linarith)
  have wB := w (a+v) (by positivity) le_rfl
  have five := nine_to_five hs hu huv hva hvb hM nine
  have six := nine_to_high hs hu huv hva hvb hM hh nine
  have inner := six_inner hu huv hva (div_pos wv wu) (div_pos wB wA) hk
    (div_pos (mul_pos hh wA) wu) five
  have vu := whi u hu.le
  have vv := whi v hv.le
  have vA := whi (b+u) (by positivity)
  have vB := whi (b+v) (by positivity)
  have last := six_inner hu huv hvb (div_pos vv vu) (div_pos vB vA) hk
    (div_pos (mul_pos hj vA) vu) six
  change _ ∧ _ ∧ _
  constructor
  · change (up u v a v * down u v a u)*(W u*W (a+v)) < (up u v a u * down u v a v)*(W v*W (a+u))
    have sm : (a+(v-u))^2*(a-u)*(a+v)*(W (a+v)*W u) <
        (a-(v-u))^2*(a-v)*(a+u)*(W v*W (a+u)) := by
      field_simp [wA.ne',wu.ne'] at inner
      linear_combination inner
    unfold up down
    linear_combination (a^2)*sm
  constructor
  · apply lt_of_not_ge
    intro he
    exact EightRootAudit.exclude_five hu huv hva (div_pos w0 wu) (div_pos wa wA)
      (div_pos wB wA) (div_pos (mul_pos hh wA) wu) he five
  · have sm : (b+(v-u))^2*(b-u)*(b+v)*(V (b+v)*V u) <
        (b-(v-u))^2*(b-v)*(b+u)*(V v*V (b+u)) := by
      field_simp [vA.ne',vu.ne'] at last
      linear_combination last
    have m : 0 < midNum u v a b u := by
      unfold midNum up down
      exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
        (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    have n : 0 < topNum u v a b v := by
      unfold topNum up
      exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
        (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
    have atS : (s+(a+u))*(s+(a+v)+b)*(midNum u v a b u*topNum u v a b v) <
         (s+(a+v))*(s+(a+u)+b)*(midNum u v a b v*topNum u v a b u) := by
      let U := up u v a u
      let X := up u v a v
      let Y := up u v (a+b) u
      let Z := up u v (a+b) v
      have a0 : V u = (s+(a+u))*U := by dsimp [V,weightH,U,up];ring
      have a1 : V v = (s+(a+v))*X := by dsimp [V,weightH,X,up];ring
      have b0 : V (b+u) = (s+(a+u)+b)*Y := by dsimp [V,weightH,Y,up];ring
      have b1 : V (b+v) = (s+(a+v)+b)*Z := by dsimp [V,weightH,Z,up];ring
      rw [a0,a1,b0,b1] at sm
      unfold midNum topNum
      change (s+(a+u))*(s+(a+v)+b)*(U*down u v b u*(Z*up u v b v)) <
        (s+(a+v))*(s+(a+u)+b)*(X*down u v b v*(Y*up u v b u))
      unfold down up
      linear_combination (b^2)*sm
    have at0 := offset hs.le (x:=a+u) (y:=a+v) (by linarith) (by linarith) hb (mul_pos m n).le atS
    linear_combination at0
#print axioms tests

def factorN (a u v i : ℝ) := (a-i)*(a+v+u-i)
def lowerN (a u v : ℝ) := factorN a u v 0 * factorN a u v u * factorN a u v v
def lowerD (a u v : ℝ) := up u v a u * up u v a v

theorem lower_eq {d u v : ℝ} (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    lower d u v = d*(d+v+u)/((d+u)*(d+v)) := by
  unfold lower
  field_simp

theorem low3_eq {a u v : ℝ} (hu : 0 < u) (huv : u < v) (hva : v < a) :
    low3 a u v = lowerN a u v / lowerD a u v := by
  have hv := hu.trans huv
  have ha := hv.trans hva
  unfold low3
  rw [lower_eq ha hu hv, lower_eq (sub_pos.mpr (huv.trans hva)) hu hv,
      lower_eq (sub_pos.mpr hva) hu hv]
  simp only [div_mul_div_comm]
  congr 1 <;> simp only [lowerN,factorN,lowerD,up] <;> ring

def testOne (s u v a b : ℝ) :=
  let W := weight s u v a b
  (up u v a v * down u v a u)*(W u*W (a+v)) -
    (up u v a u * down u v a v)*(W v*W (a+u))
def testTwo (s u v a b z : ℝ) :=
  let W := weight s u v a b
  let xd := W u*W (a+v)
  let yd := W u*W a
  (a-u)*lowerN a u v*yd*xd -
    (1-z)*a*(W 0*W (a+u))*lowerD a u v*xd -
    z*(a-v)*(W v*W (a+u))*lowerN a u v*yd
def testThree (u v a b : ℝ) :=
  ((a+u)*midNum u v a b u)*((a+b+v)*topNum u v a b v) -
    ((a+v)*midNum u v a b v)*((a+b+u)*topNum u v a b u)

theorem clear_sign {a u v z xn xd yn yd n d : ℝ}
    (hx : 0 < xd) (hy : 0 < yd) (hn : 0 < n) (_hd : 0 < d)
    (h : (a-u)-(1-z)*a*(yn/yd)/(n/d)-z*(a-v)*(xn/xd) < 0) :
    (a-u)*n*yd*xd-(1-z)*a*yn*d*xd-z*(a-v)*xn*n*yd < 0 := by
  have q := mul_neg_of_neg_of_pos h (mul_pos (mul_pos hn hy) hx)
  convert q using 1
  field_simp


theorem testTwo_neg_of_window {s u v a b : ℝ} (hs : 0 < s) (hu : 0 < u) (huv : u < v)
    (hva : v < a) (hvb : v < b)
    (h2 : let W := weight s u v a b
          (a-u) - (1-u/v)*a*((W 0/W u)/(W a/W (a+u)))/low3 a u v -
             (u/v)*(a-v)*((W v/W u)/(W (a+v)/W (a+u))) < 0) :
    testTwo s u v a b (u/v) < 0 := by
  let W := weight s u v a b
  have hv := hu.trans huv
  have ha := hv.trans hva
  have w (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ a+v) : 0 < W e := weight_pos hs hu huv hvb h0 h1
  have wu := w u hu.le (by linarith)
  have wa := w a ha.le (by linarith)
  have wb := w (a+v) (by positivity) le_rfl
  have fn (i : ℝ) (hi : i ≤ v) : 0 < factorN a u v i := by
    unfold factorN
    exact mul_pos (by linarith) (by linarith)
  have n := mul_pos (mul_pos (fn 0 hv.le) (fn u huv.le)) (fn v le_rfl)
  have upt (j : ℝ) (h0 : 0 ≤ j) : 0 < up u v a j := by
    unfold up
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have d := mul_pos (upt u hu.le) (upt v hv.le)
  apply clear_sign (mul_pos wu wb) (mul_pos wu wa) n d
  rw [low3_eq hu huv hva] at h2
  have fr (c m e n : ℝ) : (c/m)/(e/n) = (c*n)/(m*e) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [fr,W,lowerN,lowerD] using h2

theorem sign_tests {s u v a b M h j k : ℝ} (hs : 0 < s) (hu : 0 < u) (huv : u < v)
    (hva : v < a) (hvb : v < b) (hM : 0 < M) (hh : 0 < h) (hj : 0 < j) (hk : 0 < k)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    testOne s u v a b < 0 ∧ testTwo s u v a b (u/v) < 0 ∧ testThree u v a b < 0 := by
  obtain ⟨h1,h2,h3⟩ := tests hs hu huv hva hvb hM hh hj hk nine
  refine ⟨sub_neg.mpr h1, ?_, sub_neg.mpr h3⟩
  exact testTwo_neg_of_window hs hu huv hva hvb h2
#print axioms sign_tests

def AL (u v d : ℝ) := (d+v)^2*(d+u)*(d+v-u)
def AR (u v d : ℝ) := (d-v)^2*(d+u-v)*(d-u)
def highL (u v a b : ℝ) := AL u v b * (up u v a 0 * up u v (a+b) v)
def highR (u v a b : ℝ) := AR u v b * (up u v a v * up u v (a+b) 0)
def lowL (u v a b : ℝ) := AL u v a * (down u v (a+b) 0 * down u v b v)
def lowR (u v a b : ℝ) := AR u v a * (down u v (a+b) v * down u v b 0)
def highDelta (s u v a b : ℝ) :=
  (s+a)*(s+(a+v)+b)*highL u v a b - (s+(a+v))*(s+a+b)*highR u v a b
def lowDelta (s u v a b : ℝ) :=
  s*(s+v+a)*lowL u v a b - (s+v)*(s+a)*lowR u v a b

theorem outer_weight {u v d k H : ℝ} {W : ℝ → ℝ} (hu : 0 < u) (huv : u<v)
    (hvd : v<d) (w0 : 0 < W 0) (wu : 0 < W u) (wv : 0 < W v)
    (wd : 0 < W d) (wdU : 0 < W (d+u)) (wdV : 0 < W (d+v)) (hH : 0 < H)
    (five : HasZeros 5 (eval (es u v d) (cs (W 0/W u) (W v/W u)
        (W d/W (d+u)) (W (d+v)/W (d+u)) k H))) :
    AL u v d*(W 0*W (d+v)) < AR u v d*(W v*W d) := by
  have g := six_outer hu huv hvd (div_pos w0 wu) (div_pos wv wu) (div_pos wd wdU)
    (div_pos wdV wdU) hH five
  field_simp [wdU.ne',wu.ne'] at g
  unfold AL AR
  linear_combination g

theorem original_rectangles {s u v a b M h j k : ℝ} (hs : 0 < s) (hu : 0 < u)
    (huv : u < v) (hva : v < a) (hvb : v < b)
    (hM : 0 < M) (hh : 0 < h) (hj : 0 < j)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    highDelta s u v a b < 0 ∧ lowDelta s u v a b < 0 := by
  let V := weightH s u v a
  let W := weight s u v a b
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hb := hv.trans hvb
  have w (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ a+v) : 0 < W e := weight_pos hs hu huv hvb h0 h1
  have m (e : ℝ) (he : 0 ≤ e) : 0 < V e := weightH_pos hs hu huv hva he
  have hl := nine_to_five hs hu huv hva hvb hM nine
  have hr := nine_to_high hs hu huv hva hvb hM hh nine
  have goHi := outer_weight hu huv hvb (m 0 le_rfl) (m u hu.le) (m v hv.le) (m b hb.le)
    (m (b+u) (by positivity)) (m (b+v) (by positivity))
    (div_pos (mul_pos hj (m (b+u) (by positivity))) (m u hu.le)) hr
  have goLo := outer_weight hu huv hva (w 0 le_rfl (by linarith)) (w u hu.le (by linarith))
    (w v hv.le (by linarith)) (w a ha.le (by linarith)) (w (a+u) (by positivity) (by linarith))
    (w (a+v) (by positivity) le_rfl)
    (div_pos (mul_pos hh (w (a+u) (by positivity) (by linarith))) (w u hu.le (by linarith))) hl
  constructor
  · have f (e : ℝ) : V e=(s+a+e)*up u v a e := by dsimp [V,weightH,up];ring
    have f' (e : ℝ) : V (b+e)=(s+(a+e)+b)*up u v (a+b) e := by dsimp [V,weightH,up];ring
    have fb : V b=(s+a+b)*up u v (a+b) 0 := by simpa using f' 0
    rw [f 0,f v,fb,f' v] at goHi
    unfold highDelta highL highR
    linear_combination goHi
  · have f (e : ℝ) : W e=(s+e)*down u v (a+b) e := by dsimp [W,weight,down];ring
    have f' (e : ℝ) : W (a+e)=(s+a+e)*down u v b e := by dsimp [W,weight,down];ring
    have fa : W a=(s+a)*down u v b 0 := by simpa using f' 0
    rw [f 0,f v,fa,f' v] at goLo
    unfold lowDelta lowL lowR
    linear_combination goLo
#print axioms original_rectangles

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
theorem gap_poly {u w x y : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ highDelta 0 u (u+w) (u+w+x+y) (u+w+2*x) := by
  unfold highDelta highL highR AL AR up
  ring_nf
  positivity
#print axioms gap_poly

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
theorem offset_poly {u w x y : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ lowDelta (x/2) u (u+w) (u+w+x) (u+w+2*x+y) := by
  unfold lowDelta lowL lowR AL AR down
  ring_nf
  positivity
#print axioms offset_poly

theorem required_gaps {s u v a b M h j k : ℝ} (hs : 0 < s) (hu : 0 < u)
    (huv : u < v) (hva : v < a) (hvb : v < b)
    (hM : 0 < M) (hh : 0 < h) (hj : 0 < j)
    (nine : HasZeros 9 (original s u v a b M h j k)) :
    2*a-v < b ∧ s < (a-v)/2 := by
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hb := hv.trans hvb
  have upP {d e : ℝ} (h : v<d) (hh : 0 ≤ e) : 0 < up u v d e := by
    unfold up; exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have downP {d e : ℝ} (h : v<d) (hh : e≤v) : 0 < down u v d e := by
    unfold down; exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have al {d : ℝ} (hd : v<d) : 0 < AL u v d := by
    unfold AL
    exact mul_pos (mul_pos (pow_pos (by linarith) _) (by linarith)) (by linarith)
  have posHi : 0 ≤ highL u v a b :=
    (mul_pos (al hvb) (mul_pos (upP hva le_rfl) (upP (by linarith) hv.le))).le
  have posLo : 0 ≤ lowL u v a b :=
    (mul_pos (al hva) (mul_pos (downP (by linarith) hv.le) (downP hvb le_rfl))).le
  obtain ⟨H,L⟩ := original_rectangles hs hu huv hva hvb hM hh hj nine
  have H0 : highDelta 0 u v a b < 0 := by
    have h := offset hs.le (x:=a) (y:=a+v) (d:=b) ha (by linarith) hb posHi (sub_neg.mp H)
    unfold highDelta
    simpa using sub_neg.mpr h
  have gap : 2*a-v < b := by
    by_contra! no
    have w := gap_poly (u:=u) (w:=v-u) (x:=(b-v)/2) (y:=a-v-(b-v)/2)
      hu.le (by linarith) (by linarith) (by linarith)
    ring_nf at w H0
    exact (not_lt_of_ge w) H0
  refine ⟨gap,?_⟩
  by_contra! no
  let c := (a-v)/2
  have hc : 0 < c := by dsimp [c];linarith
  have h := offset (s:=s-c) (x:=c) (y:=c+v) (d:=a) (A:=lowL u v a b)
    (B:=lowR u v a b) (by dsimp [c];linarith) hc (by linarith) ha posLo (by
      change _ - _ < 0 at L
      have ll := sub_neg.mp L
      convert ll using 1 <;> ring)
  have reject : lowDelta c u v a b < 0 := sub_neg.mpr h
  have w := offset_poly (u:=u) (w:=v-u) (x:=a-v) (y:=b-2*a+v)
    hu.le (by linarith) (by linarith) (by linarith)
  dsimp [c] at reject
  ring_nf at w reject
  exact (not_lt_of_ge w) reject
#print axioms required_gaps

theorem required_signs {e c : Fin 10 → ℝ} (inc : StrictMono e) (h0 : 0 < c 0)
    (nine : HasZeros 9 (eval e c)) :
    c 1 < 0 ∧ 0 < c 2 ∧ c 3 < 0 ∧ 0 < c 4 ∧ c 7 < 0 := by
  have dp {i j : Fin 10} (h : j < i) : 0 < e i-e j := sub_pos.mpr (inc h)
  have dn {i j : Fin 10} (h : i < j) : e i-e j < 0 := sub_neg.mpr (inc h)
  have s1 : c 1 < 0 := by
    let ms := [e 2,e 3,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=2) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 1 := (mul_pos_of_neg_of_neg (dn (i:=1) (j:=2) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 1*K 1*exp (e 1*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 1*t 0)).le
    linarith only [first,second,eqn]
  have s2 : 0 < c 2 := by
    let ms := [e 1,e 3,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 2 < 0 := (mul_neg_of_pos_of_neg (dp (i:=2) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 2*K 2*exp (e 2*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 2*t 0)).le
    linarith only [first,second,eqn]
  have s3 : c 3 < 0 := by
    let ms := [e 1,e 2,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 3 := (mul_pos (dp (i:=3) (j:=1) (by decide)) (mul_pos (dp (i:=3) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 3*K 3*exp (e 3*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 3*t 0)).le
    linarith only [first,second,eqn]
  have s4 : 0 < c 4 := by
    let ms := [e 1,e 2,e 3,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 4 < 0 := (mul_neg_of_pos_of_neg (dp (i:=4) (j:=1) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=4) (j:=2) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=4) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=4) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=4) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 4*K 4*exp (e 4*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 4*t 0)).le
    linarith only [first,second,eqn]
  have s7 : c 7 < 0 := by
    let ms := [e 1,e 2,e 3,e 4,e 5,e 6,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 7 := (mul_pos (dp (i:=7) (j:=1) (by decide)) (mul_pos (dp (i:=7) (j:=2) (by decide)) (mul_pos (dp (i:=7) (j:=3) (by decide)) (mul_pos (dp (i:=7) (j:=4) (by decide)) (mul_pos (dp (i:=7) (j:=5) (by decide)) (mul_pos (dp (i:=7) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=7) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=7) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 7*K 7*exp (e 7*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 7*t 0)).le
    linarith only [first,second,eqn]
  exact ⟨s1,s2,s3,s4,s7⟩
#print axioms required_signs

noncomputable def rawProduct (s u v a b A B C D E F x : ℝ) :=
    1+exp (s*x)*(A+B*exp (a*x)+C*exp ((a+b)*x))*(D+E*exp (u*x)+F*exp (v*x))
def rawCoeff (A B C D E F : ℝ) : Fin 10 → ℝ :=
    ![1,A*D,A*E,A*F,B*D,B*E,B*F,C*D,C*E,C*F]
theorem raw_expansion (s u v a b A B C D E F t : ℝ) :
    rawProduct s u v a b A B C D E F t = eval (tenE s u v a b) (rawCoeff A B C D E F) t := by
  simp [rawProduct,eval,tenE,rawCoeff,Fin.sum_univ_succ,add_mul,exp_add]
  ring

theorem arbitrary_to_normalized {s u v a b A B C D E F : ℝ} (hs : 0 < s) (hu : 0 < u)
    (huv : u < v) (hva : v < a) (hvb : v < b)
    (nine : HasZeros 9 (rawProduct s u v a b A B C D E F)) :
    ∃ M h j k : ℝ, 0 < M ∧ 0 < h ∧ 0 < j ∧ 0 < k ∧ HasZeros 9 (original s u v a b M h j k) := by
  have inc : StrictMono (tenE s u v a b) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp [tenE] <;> linarith
  have eight : HasZeros 9 (eval (tenE s u v a b) (rawCoeff A B C D E F)) := by
    rw [← show rawProduct s u v a b A B C D E F = eval (tenE s u v a b) (rawCoeff A B C D E F) from
      funext (raw_expansion s u v a b A B C D E F)]
    exact nine
  obtain ⟨ad,ae,af,bd,cd⟩ := required_signs inc (show 0 < rawCoeff A B C D E F 0 by simp [rawCoeff]) eight
  change A*D < 0 at ad
  change 0 < A*E at ae
  change A*F < 0 at af
  change 0 < B*D at bd
  change C*D < 0 at cd
  have nzA : A ≠ 0 := left_ne_zero_of_mul ad.ne
  have nzD : D ≠ 0 := right_ne_zero_of_mul ad.ne
  have nzB : B ≠ 0 := left_ne_zero_of_mul bd.ne'
  have nzF : F ≠ 0 := right_ne_zero_of_mul af.ne
  have ratio : 0 < D/F := by
    rw [show D/F=(A*D)/(A*F) by field_simp]
    exact div_pos_of_neg_of_neg ad af
  let c := log (D/F)/v
  have hv := hu.trans huv
  have r : exp (v*c)=D/F := by
    rw [show v*c=log (D/F) by dsimp [c];field_simp, exp_log ratio]
  let M := -(A*D)*exp (s*c)
  let h := -(B/A)*exp (a*c)
  let j := -(C/B)*exp (b*c)
  let k := -(E/D)*exp (u*c)
  have ab : B/A < 0 := by
    rw [show B/A=(B*D)/(A*D) by field_simp]
    exact div_neg_of_pos_of_neg bd ad
  have cb : C/B < 0 := by
    rw [show C/B=(C*D)/(B*D) by field_simp]
    exact div_neg_of_neg_of_pos cd bd
  have ed : E/D < 0 := by
    rw [show E/D=(A*E)/(A*D) by field_simp]
    exact div_neg_of_pos_of_neg ae ad
  refine ⟨M,h,j,k,mul_pos (neg_pos.mpr ad) (exp_pos _),mul_pos (neg_pos.mpr ab) (exp_pos _),
    mul_pos (neg_pos.mpr cb) (exp_pos _),mul_pos (neg_pos.mpr ed) (exp_pos _),?_⟩
  have form (t : ℝ) : original s u v a b M h j k t = rawProduct s u v a b A B C D E F (t+c) := by
    simp only [rawProduct,original,M,h,j,k,mul_add,add_mul,exp_add,r]
    field_simp
    ring
  obtain ⟨x,incx,z⟩ := nine
  refine ⟨fun i => x i-c,fun i j hij => sub_lt_sub_right (incx hij) c,?_⟩
  intro i
  rw [form,sub_add_cancel];exact z i

theorem general_required_gaps {s u v a b A B C D E F : ℝ} (hs : 0 < s) (hu : 0 < u)
    (huv : u < v) (hva : v < a) (hvb : v < b)
    (nine : HasZeros 9 (rawProduct s u v a b A B C D E F)) :
    2*a-v < b ∧ s < (a-v)/2 := by
  obtain ⟨_,_,_,_,hm,hh,hj,_,nine'⟩ := arbitrary_to_normalized hs hu huv hva hvb nine
  exact required_gaps hs hu huv hva hvb hm hh hj nine'
#print axioms general_required_gaps

end GapAudit

namespace EightRootCoverage
def U (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1
def Lo (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1/2
def Hi (x : ℝ) : Prop := 1/2 ≤ x ∧ x ≤ 1
private theorem coords {b i s y : ℝ} (hs : 0 < s) (hsi : s ≤ i) (hib : i ≤ b)
    (hb : b ≤ 1/2) (hy : Lo y) :
    ∃ m n o h : ℝ, 0 < m ∧ 0 < n ∧ U m ∧ U n ∧ U o ∧ U h ∧
       b=m/2 ∧ i=m*n/2 ∧ y=o/2 ∧ s=m*n*h/2 := by
  have hi := hs.trans_le hsi
  have hp := hi.trans_le hib
  refine ⟨2*b,i/b,2*y,s/i,by positivity,div_pos hi hp,
    ⟨by positivity,by linarith⟩,⟨(div_pos hi hp).le,(div_le_one hp).mpr hib⟩,
    ⟨by linarith [hy.1],by linarith [hy.2]⟩,⟨(div_pos hs hi).le,(div_le_one hi).mpr hsi⟩,
    by ring,?_,by ring,?_⟩
  · field_simp
  · field_simp
theorem cover (S : ℝ → ℝ → ℝ → ℝ → Prop)
    (row1 : ∀ d z y l : ℝ, Hi d → U z → Lo y → U l → S d z y l)
    (row2 : ∀ d z y l : ℝ, Hi d → U z → Hi y → U l → S d z y l)
    (row3 : ∀ d z y l : ℝ, Lo d → U z → Hi y → U l → S d z y l)
    (row4 : ∀ d z y l : ℝ, Lo d → Hi z → Lo y → Lo l → S d z y l)
    (row5 : ∀ d z y l : ℝ, Lo d → Lo z → Lo y → Hi l → S d z y l)
    (row6 : ∀ d z y l : ℝ, Lo d → Hi z → Lo y → Hi l → S d z y l)
    (row7 : ∀ m n o h : ℝ, Lo m → U n → U o → U h → S (m/2) (m*n/2) (o/2) (m*n*h/2))
    (row8 : ∀ m n o h : ℝ, Hi m → U n → U o → U h → S (m/2) (m*n/2) (o/2) (m*n*h/2))
    (row9 : ∀ m n o h : ℝ, Lo m → U n → U o → U h → S (m/2) (m*n*h/2) (o/2) (m*n/2))
    (row10 : ∀ m n o h : ℝ, Hi m → U n → U o → U h → S (m/2) (m*n*h/2) (o/2) (m*n/2))
    (row11 : ∀ m n o h : ℝ, U m → U n → U o → U h → S (m*n/2) (m/2) (o/2) (m*n*h/2))
    (row12 : ∀ m n o h : ℝ, U m → U n → U o → U h → S (m*(m*n)/2) (m*(m*n)*h/2) (o/2) (m/2))
    (row13 : ∀ m n o h : ℝ, Lo m → U n → U o → U h → S ((m*n)*n/2) ((m*n)*n*h/2) (o/2) ((m*n)/2))
    (row14 : ∀ m n o h : ℝ, Hi m → U n → U o → U h → S ((m*n)*n/2) ((m*n)*n*h/2) (o/2) ((m*n)/2))
    (row15 : ∀ m n o h : ℝ, U m → U n → U o → U h → S (m*n*h/2) (m/2) (o/2) (m*n/2))
    (row16 : ∀ m n o h : ℝ, U m → U n → U o → U h → S (m*n*h/2) (m*n/2) (o/2) (m/2))
    {d z y l : ℝ} (hd : U d) (hz : U z) (hy : U y) (hl : U l)
    (pd : 0 < d) (pz : 0 < z) (pl : 0 < l) : S d z y l := by
  by_cases byY : y ≤ 1/2
  · have ly : Lo y := ⟨hy.1,byY⟩
    by_cases byD : d ≤ 1/2
    · have ld : Lo d := ⟨hd.1,byD⟩
      by_cases byZ : z ≤ 1/2
      · have lz : Lo z := ⟨hz.1,byZ⟩
        by_cases byL : l ≤ 1/2
        · have ll : Lo l := ⟨hl.1,byL⟩
          have case012 (h₁ : l ≤ z) (h₂ : z ≤ d) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pl h₁ h₂ byD ly
            rw [hb,hi,hy',hs]
            rcases le_total m (1/2) with hlow|hhigh
            · exact row7 _ _ _ _ ⟨hm.1,hlow⟩ hn ho hh
            · exact row8 _ _ _ _ ⟨hhigh,hm.2⟩ hn ho hh
          have case021 (h₁ : z ≤ l) (h₂ : l ≤ d) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pz h₁ h₂ byD ly
            rw [hb,hi,hy',hs]
            rcases le_total m (1/2) with hlow|hhigh
            · exact row9 _ _ _ _ ⟨hm.1,hlow⟩ hn ho hh
            · exact row10 _ _ _ _ ⟨hhigh,hm.2⟩ hn ho hh
          have case102 (h₁ : l ≤ d) (h₂ : d ≤ z) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pl h₁ h₂ byZ ly
            rw [hb,hi,hy',hs]
            exact row11 _ _ _ _ hm hn ho hh
          have case120 (h₁ : z ≤ d) (h₂ : d ≤ l) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pz h₁ h₂ byL ly
            rw [hb,hi,hy',hs]
            by_cases hnm : n ≤ m
            · have hbnd : U (n/m) := ⟨(div_pos pn pm).le,(div_le_one pm).mpr hnm⟩
              have eqn : m*(n/m)=n := by field_simp
              simpa only [eqn] using row12 m (n/m) o h hm hbnd ho hh
            · have hbnd : U (m/n) := ⟨(div_pos pm pn).le,(div_le_one pn).mpr (le_of_not_ge hnm)⟩
              have eqm : m/n*n=m := by field_simp
              rcases le_total (m/n) (1/2) with hlow|hhigh
              · simpa only [eqm] using row13 (m/n) n o h ⟨hbnd.1,hlow⟩ hn ho hh
              · simpa only [eqm] using row14 (m/n) n o h ⟨hhigh,hbnd.2⟩ hn ho hh
          have case201 (h₁ : d ≤ l) (h₂ : l ≤ z) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pd h₁ h₂ byZ ly
            rw [hb,hi,hy',hs]
            exact row15 _ _ _ _ hm hn ho hh
          have case210 (h₁ : d ≤ z) (h₂ : z ≤ l) : S d z y l := by
            obtain ⟨m,n,o,h,pm,pn,hm,hn,ho,hh,hb,hi,hy',hs⟩ := coords pd h₁ h₂ byL ly
            rw [hb,hi,hy',hs]
            exact row16 _ _ _ _ hm hn ho hh
          rcases le_total d z with hdz|hzd
          · rcases le_total z l with hzl|hlz
            · exact case210 hdz hzl
            · rcases le_total d l with hdl|hld
              · exact case201 hdl hlz
              · exact case102 hld hdz
          · rcases le_total d l with hdl|hld
            · exact case120 hzd hdl
            · rcases le_total z l with hzl|hlz
              · exact case021 hzl hld
              · exact case012 hlz hzd
        · exact row5 _ _ _ _ ld lz ly ⟨le_of_not_ge byL,hl.2⟩
      · have zz : Hi z := ⟨le_of_not_ge byZ,hz.2⟩
        rcases le_total l (1/2) with hlo|hhi
        · exact row4 _ _ _ _ ld zz ly ⟨hl.1,hlo⟩
        · exact row6 _ _ _ _ ld zz ly ⟨hhi,hl.2⟩
    · exact row1 _ _ _ _ ⟨le_of_not_ge byD,hd.2⟩ hz ly hl
  · have yy : Hi y := ⟨le_of_not_ge byY,hy.2⟩
    rcases le_total d (1/2) with hlo|hhi
    · exact row3 _ _ _ _ ⟨hd.1,hlo⟩ hz yy hl
    · exact row2 _ _ _ _ ⟨hhi,hd.2⟩ hz yy hl
#print axioms cover

/-- Recovery of the five exponents up to one common positive scale. -/
theorem normalize {u v a b s : ℝ} (hu : 0 < u) (huv : u < v) (hva : v < a)
    (hb : 2*a-v < b) (hs : 0 < s) (hoff : s < (a-v)/2) :
    let d := 1-v/a
    let z := u/v
    let y := 2*s/(a-v)
    let l := 1-(2*a-v)/b
    let c := 2*(1-l)/a
    0 < d ∧ d < 1 ∧ 0 < z ∧ z < 1 ∧ 0 < y ∧ y < 1 ∧ 0 < l ∧ l < 1 ∧ 0 < c ∧
    2*(1-l) = c*a ∧ 2*(1-l)*(1-d)=c*v ∧ z*(2*(1-l)*(1-d))=c*u ∧
    2*(1+d)=c*b ∧ d*y*(1-l)=c*s := by
  dsimp only
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hav := sub_pos.mpr hva
  have h2 : 0 < 2*a-v := by linarith
  have bpos := h2.trans hb
  have pv := div_pos hv ha
  have pz := div_pos hu hv
  have py := div_pos (show 0 < 2*s by positivity) hav
  have pb := div_pos h2 bpos
  have pd := (div_lt_one ha).mpr hva
  have pl := (div_lt_one bpos).mpr hb
  have py' := (div_lt_one hav).mpr (show 2*s < a-v by linarith)
  refine ⟨by linarith,by linarith,pz,(div_lt_one hv).mpr huv,py,py',by linarith,by linarith,
      ?_,?_,?_,?_,?_,?_⟩
  · apply div_pos _ ha
    linarith
  all_goals field_simp <;> ring
#print axioms normalize

end EightRootCoverage

namespace GapAudit
open Real Set SparseProductRoots EightRootAudit

def inChart (d z y l : ℝ) :=
  let a := 2*(1-l)
  let v := a*(1-d)
  let u := z*v
  let b := 2*(1+d)
  let s := d*y*(1-l)
  0 ≤ testOne s u v a b ∨ 0 ≤ testTwo s u v a b z ∨ 0 ≤ testThree u v a b

theorem change_scale {r s u v a b M h j k : ℝ} (hr : 0<r)
    (roots : HasZeros 9 (original s u v a b M h j k)) :
    HasZeros 9 (original (r*s) (r*u) (r*v) (r*a) (r*b) M h j k) := by
  obtain ⟨x,inc,hx⟩ := roots
  refine ⟨fun i => x i/r,fun i j h => (div_lt_div_iff_of_pos_right hr).mpr (inc h),?_⟩
  intro i
  have scale (f : ℝ) : r*f*(x i/r)=f*x i := by field_simp
  unfold original at *
  rw [←mul_add r a b,scale,scale,scale,scale,scale]
  exact hx i

theorem general_from_cube
    (cube : ∀ d z y l : ℝ, d ∈ Set.Ioo 0 1 → z ∈ Set.Ioo 0 1 →
      y ∈ Set.Ioo 0 1 → l ∈ Set.Ioo 0 1 → inChart d z y l)
    {s u v a b A B C D E F : ℝ} (hs : 0 < s) (hu : 0 < u) (huv : u < v)
    (hva : v < a) (hvb : v < b) :
    ¬ HasZeros 9 (rawProduct s u v a b A B C D E F) := by
  intro nine
  obtain ⟨M,h,j,k,hM,hh,hj,hk,h9⟩ := arbitrary_to_normalized hs hu huv hva hvb nine
  obtain ⟨bg,so⟩ := required_gaps hs hu huv hva hvb hM hh hj h9
  let d := 1-v/a
  let z := u/v
  let y := 2*s/(a-v)
  let l := 1-(2*a-v)/b
  let c := 2*(1-l)/a
  have norm := EightRootCoverage.normalize hu huv hva bg hs so
  change 0 < d ∧ d < 1 ∧ 0 < z ∧ z < 1 ∧ 0 < y ∧ y < 1 ∧ 0 < l ∧ l < 1 ∧ 0 < c ∧
    2*(1-l) = c*a ∧ 2*(1-l)*(1-d)=c*v ∧ z*(2*(1-l)*(1-d))=c*u ∧
    2*(1+d)=c*b ∧ d*y*(1-l)=c*s at norm
  obtain ⟨d0,d1,z0,z1,y0,y1,l0,l1,c0,eA,eV,eU,eB,eS⟩ := norm
  have pass := cube d z y l ⟨d0,d1⟩ ⟨z0,z1⟩ ⟨y0,y1⟩ ⟨l0,l1⟩
  unfold inChart at pass
  dsimp only at pass
  rw [eU,eV,eA,eB,eS] at pass
  have hc9 := change_scale c0 h9
  have bad := sign_tests (mul_pos c0 hs) (mul_pos c0 hu)
    (mul_lt_mul_of_pos_left huv c0) (mul_lt_mul_of_pos_left hva c0)
    (mul_lt_mul_of_pos_left hvb c0) hM hh hj hk hc9
  have zscale : c*u/(c*v) = z := by dsimp [z];field_simp
  rw [zscale] at bad
  rcases pass with good|good|good
  · exact (not_lt_of_ge good) bad.1
  · exact (not_lt_of_ge good) bad.2.1
  · exact (not_lt_of_ge good) bad.2.2
#print axioms general_from_cube

theorem restrict_roots {m n : ℕ} {f : ℝ → ℝ} (le : m ≤ n) (h : HasZeros n f) :
    HasZeros m f := by
  obtain ⟨x,inc,hx⟩ := h
  exact ⟨fun i => x (i.castLE le),inc.comp (Fin.strictMono_castLE le),fun i => hx _⟩

theorem short_support {ι : Type*} [Fintype ι] (w c : ι → ℝ) {n : ℕ}
    (hc : (Finset.univ.image w).card ≤ n) (roots : HasZeros n (eval w c)) :
    ∀ t, eval w c t=0 := by
  classical
  let E := Finset.univ.image w
  have inE (i : ι) : w i ∈ E := Finset.mem_image_of_mem w (Finset.mem_univ _)
  have grp (e : ℝ) (he : e ∈ E) : (∑ i : ι with w i = e, c i) = 0 := by
    let L := (E.erase e).toList
    have hl : 1+L.length ≤ n := by
      dsimp only [L]
      rw [Finset.length_toList, Finset.card_erase_of_mem he]
      have := Finset.card_pos.mpr ⟨e,he⟩
      change E.card ≤ n at hc
      omega
    obtain ⟨x,_,h⟩ := remove_many (n:=1) w c L (restrict_roots hl roots)
    let K (f : ℝ) := (L.map (fun m => f-m)).prod
    have keep : K e ≠ 0 := by
      apply List.prod_ne_zero
      intro hh
      obtain ⟨m,hm,eq⟩ := List.mem_map.mp hh
      have hne := (Finset.mem_erase.mp (Finset.mem_toList.mp hm)).1
      exact hne (sub_eq_zero.mp eq).symm
    have kill (i : ι) (ne : w i ≠ e) : K (w i) = 0 := by
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨w i,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨ne,inE i⟩),sub_self _⟩
    have zero : (∑ i : ι, c i*K (w i)*exp (w i*x 0)) = 0 := h 0
    have eqn : (∑ i : ι with w i=e, c i)*(K e*exp (e*x 0)) = 0 := by
      rw [← zero, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases eq : w i=e
      · simp [eq,mul_assoc]
      · simp [eq,kill i eq]
    exact (mul_eq_zero.mp eqn).resolve_right (mul_ne_zero keep (exp_pos _).ne')
  intro t
  unfold eval
  rw [← Finset.sum_fiberwise_of_maps_to (s:=Finset.univ) (t:=E) (g:=w) (fun i _ => inE i)]
  apply Finset.sum_eq_zero
  intro e he
  calc
    _ = (∑ i : ι with w i=e,c i)*exp (e*t) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = 0 := by rw [grp e he,zero_mul]

theorem distinct_ten {w c : Fin 10 → ℝ} (roots : HasZeros 9 (eval w c))
    (nz : ∃ t, eval w c t ≠ 0) : Function.Injective w := by
  classical
  by_contra no
  have ne : (Finset.univ.image w).card ≠ 10 := by
    intro eq
    apply no
    apply Set.injOn_univ.mp
    have ord := (Finset.card_image_iff (s:=(Finset.univ : Finset (Fin 10))) (f:=w)).mp (by simpa using eq)
    simpa using ord
  have bnd := Finset.card_image_le (s:=(Finset.univ : Finset (Fin 10))) (f:=w)
  have bnd' : (Finset.univ.image w).card ≤ 9 := by simp at bnd;omega
  obtain ⟨t,nt⟩ := nz
  exact nt (short_support w c bnd' roots t)
#print axioms distinct_ten

theorem signs_by_position {e c : Fin 10 → ℝ} (inc : StrictMono e) (h0 : 0 < c 0)
    (nine : HasZeros 9 (eval e c)) :
    ∀ i : Fin 9, if i.val%2=0 then c i.succ < 0 else 0 < c i.succ := by
  have dp {i j : Fin 10} (h : j < i) : 0 < e i-e j := sub_pos.mpr (inc h)
  have dn {i j : Fin 10} (h : i < j) : e i-e j < 0 := sub_neg.mpr (inc h)
  have s1 : c 1 < 0 := by
    let ms := [e 2,e 3,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=2) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 1 := (mul_pos_of_neg_of_neg (dn (i:=1) (j:=2) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=1) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=1) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 1*K 1*exp (e 1*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 1*t 0)).le
    linarith only [first,second,eqn]
  have s2 : 0 < c 2 := by
    let ms := [e 1,e 3,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 2 < 0 := (mul_neg_of_pos_of_neg (dp (i:=2) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=3) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=2) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=2) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 2*K 2*exp (e 2*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 2*t 0)).le
    linarith only [first,second,eqn]
  have s3 : c 3 < 0 := by
    let ms := [e 1,e 2,e 4,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 3 := (mul_pos (dp (i:=3) (j:=1) (by decide)) (mul_pos (dp (i:=3) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=4) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=3) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=3) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 3*K 3*exp (e 3*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 3*t 0)).le
    linarith only [first,second,eqn]
  have s4 : 0 < c 4 := by
    let ms := [e 1,e 2,e 3,e 5,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 4 < 0 := (mul_neg_of_pos_of_neg (dp (i:=4) (j:=1) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=4) (j:=2) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=4) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=5) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=4) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=4) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=4) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 4*K 4*exp (e 4*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 4*t 0)).le
    linarith only [first,second,eqn]
  have s5 : c 5 < 0 := by
    let ms := [e 1,e 2,e 3,e 4,e 6,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 5 := (mul_pos (dp (i:=5) (j:=1) (by decide)) (mul_pos (dp (i:=5) (j:=2) (by decide)) (mul_pos (dp (i:=5) (j:=3) (by decide)) (mul_pos (dp (i:=5) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=5) (j:=6) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=5) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=5) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=5) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 5*K 5*exp (e 5*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 5*t 0)).le
    linarith only [first,second,eqn]
  have s6 : 0 < c 6 := by
    let ms := [e 1,e 2,e 3,e 4,e 5,e 7,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 6 < 0 := (mul_neg_of_pos_of_neg (dp (i:=6) (j:=1) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=6) (j:=2) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=6) (j:=3) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=6) (j:=4) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=6) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=6) (j:=7) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=6) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=6) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 6*K 6*exp (e 6*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 6*t 0)).le
    linarith only [first,second,eqn]
  have s7 : c 7 < 0 := by
    let ms := [e 1,e 2,e 3,e 4,e 5,e 6,e 8,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 7 := (mul_pos (dp (i:=7) (j:=1) (by decide)) (mul_pos (dp (i:=7) (j:=2) (by decide)) (mul_pos (dp (i:=7) (j:=3) (by decide)) (mul_pos (dp (i:=7) (j:=4) (by decide)) (mul_pos (dp (i:=7) (j:=5) (by decide)) (mul_pos (dp (i:=7) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=7) (j:=8) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=7) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 7*K 7*exp (e 7*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 7*t 0)).le
    linarith only [first,second,eqn]
  have s8 : 0 < c 8 := by
    let ms := [e 1,e 2,e 3,e 4,e 5,e 6,e 7,e 9]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=7) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : K 8 < 0 := (mul_neg_of_pos_of_neg (dp (i:=8) (j:=1) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=2) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=3) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=4) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=5) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=6) (by decide)) (mul_neg_of_pos_of_neg (dp (i:=8) (j:=7) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=8) (j:=9) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 8*K 8*exp (e 8*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos bad hpj.le) (exp_pos (e 8*t 0)).le
    linarith only [first,second,eqn]
  have s9 : c 9 < 0 := by
    let ms := [e 1,e 2,e 3,e 4,e 5,e 6,e 7,e 8]
    obtain ⟨t,_,h⟩ := remove_many (n:=1) e c ms nine
    let K (i : Fin 10) := (ms.map (fun m => e i-m)).prod
    have hp0 : 0 < K 0 := (mul_pos_of_neg_of_neg (dn (i:=0) (j:=1) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=2) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=3) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=4) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=5) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=6) (by decide)) (mul_pos_of_neg_of_neg (dn (i:=0) (j:=7) (by decide)) (mul_neg_of_neg_of_pos (dn (i:=0) (j:=8) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have hpj : 0 < K 9 := (mul_pos (dp (i:=9) (j:=1) (by decide)) (mul_pos (dp (i:=9) (j:=2) (by decide)) (mul_pos (dp (i:=9) (j:=3) (by decide)) (mul_pos (dp (i:=9) (j:=4) (by decide)) (mul_pos (dp (i:=9) (j:=5) (by decide)) (mul_pos (dp (i:=9) (j:=6) (by decide)) (mul_pos (dp (i:=9) (j:=7) (by decide)) (mul_pos (dp (i:=9) (j:=8) (by decide)) (by norm_num : (0:ℝ)<1)))))))))
    have zero : (∑ i, c i*K i*exp (e i*t 0)) = 0 := h 0
    have eqn : c 0*K 0*exp (e 0*t 0)+c 9*K 9*exp (e 9*t 0)=0 := by
      rw [←zero]
      simp [Fin.sum_univ_succ,ms,K]
    have first := mul_pos (mul_pos h0 hp0) (exp_pos (e 0*t 0))
    by_contra! bad
    have second := mul_nonneg (mul_nonneg bad hpj.le) (exp_pos (e 9*t 0)).le
    linarith only [first,second,eqn]
  intro i
  fin_cases i <;> first | exact s1 | exact s2 | exact s3 | exact s4 | exact s5 | exact s6 | exact s7 | exact s8 | exact s9

noncomputable def tenFun (e c : Fin 9 → ℝ) (t : ℝ) := 1 + eval e c t
theorem tenLift (e c : Fin 9 → ℝ) :
    tenFun e c = eval (Fin.cases 0 e) (Fin.cases 1 c) := by
  funext t
  simp [tenFun,eval,Fin.sum_univ_succ]

theorem order_equiv {e : Fin 9 → ℝ} (inj : Function.Injective e) :
    ∃ p : Fin 9 ≃ Fin 9, StrictMono (fun i => e (p i)) := by
  classical
  let S := Finset.univ.image e
  have card : S.card=9 := by simpa [S] using Finset.card_image_of_injective Finset.univ inj
  let o := S.orderIsoOfFin card
  let f (i : Fin 9) : {y // y ∈ S} := ⟨e i,Finset.mem_image_of_mem e (Finset.mem_univ _)⟩
  have bf : Function.Bijective f := by
    constructor
    · intro i j eq
      exact inj (congrArg Subtype.val eq)
    · rintro ⟨y,hy⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hy
      exact ⟨i,Subtype.ext hi⟩
  let q := Equiv.ofBijective f bf
  let p := o.toEquiv.trans q.symm
  have val (i : Fin 9) : e (p i) = (o i).val := congrArg Subtype.val (q.apply_symm_apply (o i))
  exact ⟨p,fun i j hij => by change e (p i)<e (p j);rw [val,val];exact o.strictMono hij⟩

theorem ranked_signs {e c : Fin 9 → ℝ} (epos : ∀ i, 0 < e i)
    (inj : Function.Injective e) (nine : HasZeros 9 (tenFun e c)) :
    ∃ r : Fin 9 ≃ Fin 9, (∀ i j, r i < r j ↔ e i < e j) ∧
       ∀ i, if (r i).val%2=0 then c i<0 else 0<c i := by
  obtain ⟨p,sorted⟩ := order_equiv inj
  let E : Fin 10 → ℝ := Fin.cases 0 (fun i => e (p i))
  let C : Fin 10 → ℝ := Fin.cases 1 (fun i => c (p i))
  have inc : StrictMono E := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact epos (p 0)
    · exact sorted (Fin.castSucc_lt_succ (i:=j))
  have eqn : eval E C = tenFun e c := by
    funext t
    change eval (Fin.cases 0 (fun i => e (p i))) (Fin.cases 1 (fun i => c (p i))) t=_
    rw [←tenLift]
    unfold tenFun eval
    rw [p.sum_comp (fun i => c i * exp (e i*t))]
  have sign := signs_by_position inc (show 0 < C 0 by norm_num [C]) (eqn.symm ▸ nine)
  refine ⟨p.symm,?_,?_⟩
  · intro i j
    simpa only [Equiv.apply_symm_apply] using (sorted.lt_iff_lt (a:=p.symm i) (b:=p.symm j)).symm
  · intro i
    simpa [C] using sign (p.symm i)
#print axioms ranked_signs

theorem even_rectangle {i j k l : ℕ} {A B C D : ℝ}
    (sa : if i%2=0 then A<0 else 0<A) (sb : if j%2=0 then B<0 else 0<B)
    (sc : if k%2=0 then C<0 else 0<C) (sd : if l%2=0 then D<0 else 0<D)
    (equ : A*D=B*C) : (i+j+k+l)%2=0 := by
  have split (n : ℕ) : n%2=0 ∨ n%2=1 := by omega
  rcases split i with a|a <;> rcases split j with b|b <;> rcases split k with c|c <;>
    rcases split l with d|d
  all_goals try omega
  all_goals simp [a,b,c,d] at sa sb sc sd
  all_goals
    first
    | exact False.elim ((ne_of_lt ((mul_neg_of_neg_of_pos sa sd).trans (mul_pos_of_neg_of_neg sb sc))) equ)
    | exact False.elim ((ne_of_lt ((mul_neg_of_pos_of_neg sa sd).trans (mul_pos_of_neg_of_neg sb sc))) equ)
    | exact False.elim ((ne_of_lt ((mul_neg_of_neg_of_pos sa sd).trans (mul_pos sb sc))) equ)
    | exact False.elim ((ne_of_lt ((mul_neg_of_pos_of_neg sa sd).trans (mul_pos sb sc))) equ)
    | exact False.elim ((ne_of_lt ((mul_neg_of_neg_of_pos sb sc).trans (mul_pos_of_neg_of_neg sa sd))) equ.symm)
    | exact False.elim ((ne_of_lt ((mul_neg_of_pos_of_neg sb sc).trans (mul_pos_of_neg_of_neg sa sd))) equ.symm)
    | exact False.elim ((ne_of_lt ((mul_neg_of_neg_of_pos sb sc).trans (mul_pos sa sd))) equ.symm)
    | exact False.elim ((ne_of_lt ((mul_neg_of_pos_of_neg sb sc).trans (mul_pos sa sd))) equ.symm)

private theorem nine_chain {a b c d e f g h i : ℕ}
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f)
    (h6 : f < g) (h7 : g < h) (h8 : h < i) (hi : i < 9) :
    a=0 ∧ b=1 ∧ c=2 ∧ d=3 ∧ e=4 ∧ f=5 ∧ g=6 ∧ h=7 ∧ i=8 := by omega
set_option maxHeartbeats 2000000 in
private theorem grid_rank (r : Fin 9 → ℕ) (inj : Function.Injective r) (bound : ∀ i, r i < 9)
    (h01 : r 0 < r 1)
    (h03 : r 0 < r 3)
    (h12 : r 1 < r 2)
    (h14 : r 1 < r 4)
    (h25 : r 2 < r 5)
    (h34 : r 3 < r 4)
    (h36 : r 3 < r 6)
    (h45 : r 4 < r 5)
    (h47 : r 4 < r 7)
    (h58 : r 5 < r 8)
    (h67 : r 6 < r 7)
    (h78 : r 7 < r 8)
    (p0 : (r 0+r 3+r 1+r 4)%2=0)
    (p1 : (r 0+r 3+r 2+r 5)%2=0)
    (p2 : (r 0+r 6+r 1+r 7)%2=0)
    (p3 : (r 0+r 6+r 2+r 8)%2=0)
    : (r 2 < r 3 ∧ r 5 < r 6) ∨ (r 6 < r 1 ∧ r 7 < r 2) := by
  rcases lt_or_gt_of_ne (inj.ne (by decide : (1:Fin 9) ≠ 3)) with h13|h31
  · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 3)) with h23|h32
    · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 6)) with h56|h65
        · exact Or.inl ⟨h23,h56⟩
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
          · obtain ⟨k0,_,k2,k3,_,_,k5,_,_⟩ := nine_chain h01 h12 h23 h34 h46 h65 h57 h78 (bound 8)
            norm_num [k0,k3,k2,k5] at p1
          · obtain ⟨k0,_,k2,_,_,k6,_,_,k8⟩ := nine_chain h01 h12 h23 h34 h46 h67 h75 h58 (bound 8)
            norm_num [k0,k6,k2,k8] at p3
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
        · obtain ⟨k0,k1,_,k3,_,k4,_,_,_⟩ := nine_chain h01 h12 h23 h36 h64 h45 h57 h78 (bound 8)
          norm_num [k0,k3,k1,k4] at p0
        · obtain ⟨k0,k1,_,k3,_,k4,_,_,_⟩ := nine_chain h01 h12 h23 h36 h64 h47 h75 h58 (bound 8)
          norm_num [k0,k3,k1,k4] at p0
    · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 4)) with h24|h42
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 6)) with h26|h62
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 6)) with h56|h65
            · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h32 h24 h45 h56 h67 h78 (bound 8)
              norm_num [k0,k3,k1,k4] at p0
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h32 h24 h46 h65 h57 h78 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
              · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h32 h24 h46 h67 h75 h58 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
            · obtain ⟨k0,_,k3,k2,_,_,k5,_,_⟩ := nine_chain h01 h13 h32 h26 h64 h45 h57 h78 (bound 8)
              norm_num [k0,k3,k2,k5] at p1
            · obtain ⟨k0,k1,_,_,k6,_,k7,_,_⟩ := nine_chain h01 h13 h32 h26 h64 h47 h75 h58 (bound 8)
              norm_num [k0,k6,k1,k7] at p2
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
          · obtain ⟨k0,k1,_,k6,_,_,_,k7,_⟩ := nine_chain h01 h13 h36 h62 h24 h45 h57 h78 (bound 8)
            norm_num [k0,k6,k1,k7] at p2
          · obtain ⟨k0,_,k3,_,k2,_,_,k5,_⟩ := nine_chain h01 h13 h36 h62 h24 h47 h75 h58 (bound 8)
            norm_num [k0,k3,k2,k5] at p1
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 6)) with h26|h62
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 6)) with h56|h65
          · obtain ⟨k0,_,k3,_,k2,k5,_,_,_⟩ := nine_chain h01 h13 h34 h42 h25 h56 h67 h78 (bound 8)
            norm_num [k0,k3,k2,k5] at p1
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
            · obtain ⟨k0,k1,_,_,_,k6,_,k7,_⟩ := nine_chain h01 h13 h34 h42 h26 h65 h57 h78 (bound 8)
              norm_num [k0,k6,k1,k7] at p2
            · obtain ⟨k0,_,k3,_,k2,_,_,k5,_⟩ := nine_chain h01 h13 h34 h42 h26 h67 h75 h58 (bound 8)
              norm_num [k0,k3,k2,k5] at p1
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 7)) with h27|h72
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,_,k3,_,_,k2,k5,_,_⟩ := nine_chain h01 h13 h34 h46 h62 h25 h57 h78 (bound 8)
                norm_num [k0,k3,k2,k5] at p1
              · obtain ⟨k0,k1,_,_,k6,_,k7,_,_⟩ := nine_chain h01 h13 h34 h46 h62 h27 h75 h58 (bound 8)
                norm_num [k0,k6,k1,k7] at p2
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h36 h64 h42 h25 h57 h78 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
              · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h36 h64 h42 h27 h75 h58 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
            · obtain ⟨k0,_,k3,_,_,_,k2,k5,_⟩ := nine_chain h01 h13 h34 h46 h67 h72 h25 h58 (bound 8)
              norm_num [k0,k3,k2,k5] at p1
            · obtain ⟨k0,k1,k3,_,k4,_,_,_,_⟩ := nine_chain h01 h13 h36 h64 h47 h72 h25 h58 (bound 8)
              norm_num [k0,k3,k1,k4] at p0
  · rcases lt_or_gt_of_ne (inj.ne (by decide : (1:Fin 9) ≠ 6)) with h16|h61
    · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 4)) with h24|h42
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 6)) with h26|h62
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 6)) with h56|h65
            · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h12 h24 h45 h56 h67 h78 (bound 8)
              norm_num [k0,k3,k1,k4] at p0
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h12 h24 h46 h65 h57 h78 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
              · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h12 h24 h46 h67 h75 h58 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
            · obtain ⟨k0,_,k1,_,k6,_,_,k7,_⟩ := nine_chain h03 h31 h12 h26 h64 h45 h57 h78 (bound 8)
              norm_num [k0,k6,k1,k7] at p2
            · obtain ⟨k0,k3,_,k2,_,_,_,k5,_⟩ := nine_chain h03 h31 h12 h26 h64 h47 h75 h58 (bound 8)
              norm_num [k0,k3,k2,k5] at p1
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
          · obtain ⟨k0,k3,_,_,k2,_,k5,_,_⟩ := nine_chain h03 h31 h16 h62 h24 h45 h57 h78 (bound 8)
            norm_num [k0,k3,k2,k5] at p1
          · obtain ⟨k0,_,k1,k6,_,_,k7,_,_⟩ := nine_chain h03 h31 h16 h62 h24 h47 h75 h58 (bound 8)
            norm_num [k0,k6,k1,k7] at p2
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 6)) with h26|h62
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 6)) with h56|h65
          · obtain ⟨k0,_,k1,_,_,_,k6,k7,_⟩ := nine_chain h03 h31 h14 h42 h25 h56 h67 h78 (bound 8)
            norm_num [k0,k6,k1,k7] at p2
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
            · obtain ⟨k0,k3,_,_,k2,_,k5,_,_⟩ := nine_chain h03 h31 h14 h42 h26 h65 h57 h78 (bound 8)
              norm_num [k0,k3,k2,k5] at p1
            · obtain ⟨k0,_,k1,_,_,k6,k7,_,_⟩ := nine_chain h03 h31 h14 h42 h26 h67 h75 h58 (bound 8)
              norm_num [k0,k6,k1,k7] at p2
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 7)) with h27|h72
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,_,k1,_,k6,_,_,k7,_⟩ := nine_chain h03 h31 h14 h46 h62 h25 h57 h78 (bound 8)
                norm_num [k0,k6,k1,k7] at p2
              · obtain ⟨k0,k3,_,_,_,k2,_,k5,_⟩ := nine_chain h03 h31 h14 h46 h62 h27 h75 h58 (bound 8)
                norm_num [k0,k3,k2,k5] at p1
            · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
              · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h16 h64 h42 h25 h57 h78 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
              · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h16 h64 h42 h27 h75 h58 (bound 8)
                norm_num [k0,k3,k1,k4] at p0
          · rcases lt_or_gt_of_ne (inj.ne (by decide : (4:Fin 9) ≠ 6)) with h46|h64
            · obtain ⟨k0,_,k1,_,k6,k7,_,_,_⟩ := nine_chain h03 h31 h14 h46 h67 h72 h25 h58 (bound 8)
              norm_num [k0,k6,k1,k7] at p2
            · obtain ⟨k0,k3,k1,_,k4,_,_,_,_⟩ := nine_chain h03 h31 h16 h64 h47 h72 h25 h58 (bound 8)
              norm_num [k0,k3,k1,k4] at p0
    · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 4)) with h24|h42
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
        · obtain ⟨k0,k3,_,k1,_,k4,_,_,_⟩ := nine_chain h03 h36 h61 h12 h24 h45 h57 h78 (bound 8)
          norm_num [k0,k3,k1,k4] at p0
        · obtain ⟨k0,k3,_,k1,_,k4,_,_,_⟩ := nine_chain h03 h36 h61 h12 h24 h47 h75 h58 (bound 8)
          norm_num [k0,k3,k1,k4] at p0
      · rcases lt_or_gt_of_ne (inj.ne (by decide : (2:Fin 9) ≠ 7)) with h27|h72
        · rcases lt_or_gt_of_ne (inj.ne (by decide : (5:Fin 9) ≠ 7)) with h57|h75
          · obtain ⟨k0,_,k6,_,_,k2,_,_,k8⟩ := nine_chain h03 h36 h61 h14 h42 h25 h57 h78 (bound 8)
            norm_num [k0,k6,k2,k8] at p3
          · obtain ⟨k0,k3,_,_,_,k2,_,k5,_⟩ := nine_chain h03 h36 h61 h14 h42 h27 h75 h58 (bound 8)
            norm_num [k0,k3,k2,k5] at p1
        · exact Or.inr ⟨h61,h72⟩

def cellE (s u v a b : ℝ) : Fin 9 → ℝ :=
    ![s,s+u,s+v,s+a,s+(a+u),s+(a+v),s+(a+b),s+(a+b+u),s+(a+b+v)]
def cellC (A B C D E F : ℝ) : Fin 9 → ℝ :=
    ![A*D,A*E,A*F,B*D,B*E,B*F,C*D,C*E,C*F]

theorem the_shapes {s u v a b A B C D E F : ℝ}
    (hs : 0 ≤ s) (hu : 0 < u) (huv : u < v) (ha : 0 < a) (hb : 0 < b)
    (nz : ∃ t, rawProduct s u v a b A B C D E F t ≠ 0)
    (nine : HasZeros 9 (rawProduct s u v a b A B C D E F)) :
    0 < s ∧ ((v<a ∧ v<b) ∨ (a+b<u ∧ a+b<v-u)) := by
  let e := cellE s u v a b
  let c := cellC A B C D E F
  have eqn : rawProduct s u v a b A B C D E F = tenFun e c := by
    funext t
    simp [rawProduct,tenFun,eval,e,c,cellE,cellC,Fin.sum_univ_succ,add_mul,exp_add]
    ring
  rw [eqn] at nz nine
  have inj : Function.Injective (Fin.cases (motive:=fun _ : Fin 10 => ℝ) 0 e) := by
    rw [tenLift] at nz nine
    exact distinct_ten nine nz
  have pos : 0 < s := by
    have hn := inj.ne (show (0 : Fin 10) ≠ 1 by decide)
    change 0 ≠ s at hn
    exact lt_of_le_of_ne hs hn
  refine ⟨pos,?_⟩
  have ei : Function.Injective e := by
    intro i j hh
    exact Fin.succ_injective _ (inj (a₁:=i.succ) (a₂:=j.succ) hh)
  have ep (i : Fin 9) : 0 < e i := by
    fin_cases i <;> simp [e,cellE] <;> linarith
  obtain ⟨r,ordered,sign⟩ := ranked_signs ep ei nine
  let n (i : Fin 9) := (r i).val
  have ni : Function.Injective n := fun _ _ h => r.injective (Fin.ext h)
  have eord (i j : Fin 9) : n i < n j ↔ e i < e j := ordered i j
  have h01 : n 0 < n 1 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h03 : n 0 < n 3 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h12 : n 1 < n 2 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h14 : n 1 < n 4 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h25 : n 2 < n 5 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h34 : n 3 < n 4 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h36 : n 3 < n 6 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h45 : n 4 < n 5 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h47 : n 4 < n 7 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h58 : n 5 < n 8 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h67 : n 6 < n 7 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have h78 : n 7 < n 8 := (eord _ _).mpr (by simp [e,cellE];linarith)
  have r0 := even_rectangle (sign 0) (sign 3) (sign 1) (sign 4) (by dsimp [c,cellC];ring : c 0*c 4=c 3*c 1)
  have r1 := even_rectangle (sign 0) (sign 3) (sign 2) (sign 5) (by dsimp [c,cellC];ring : c 0*c 5=c 3*c 2)
  have r2 := even_rectangle (sign 0) (sign 6) (sign 1) (sign 7) (by dsimp [c,cellC];ring : c 0*c 7=c 6*c 1)
  have r3 := even_rectangle (sign 0) (sign 6) (sign 2) (sign 8) (by dsimp [c,cellC];ring : c 0*c 8=c 6*c 2)
  rcases grid_rank n ni (fun i => (r i).isLt) h01 h03 h12 h14 h25 h34 h36 h45 h47 h58 h67 h78 r0 r1 r2 r3 with ⟨one,two⟩|⟨one,two⟩
  · have o := (eord _ _).mp one
    have p := (eord _ _).mp two
    simp [e,cellE] at o p
    exact Or.inl ⟨by linarith,by linarith⟩
  · have o := (eord _ _).mp one
    have p := (eord _ _).mp two
    simp [e,cellE] at o p
    exact Or.inr ⟨by linarith,by linarith⟩
#print axioms the_shapes

theorem general_product_from_cube
    (cube : ∀ d z y l : ℝ, d ∈ Set.Ioo 0 1 → z ∈ Set.Ioo 0 1 →
        y ∈ Set.Ioo 0 1 → l ∈ Set.Ioo 0 1 → inChart d z y l)
    {s u v a b A B C D E F : ℝ} (hs : 0 ≤ s) (hu : 0 < u) (huv : u < v)
    (ha : 0 < a) (hb : 0 < b)
    (nz : ∃ t, rawProduct s u v a b A B C D E F t ≠ 0) :
    ¬ HasZeros 9 (rawProduct s u v a b A B C D E F) := by
  intro nine
  obtain ⟨pos,lr|tb⟩ := the_shapes hs hu huv ha hb nz nine
  · exact general_from_cube cube pos hu huv lr.1 lr.2 nine
  · have swap : rawProduct s u v a b A B C D E F =
          rawProduct s a (a+b) u (v-u) D E F A B C := by
      funext t
      unfold rawProduct
      rw [show u+(v-u)=v by ring]
      ring
    rw [swap] at nine
    exact general_from_cube cube pos ha (by linarith) tb.1 tb.2 nine
#print axioms general_product_from_cube

theorem three_terms (f : Polynomial ℝ) (hf : f.support.card ≤ 3) :
    ∃ m u v A B C : ℝ, 0 ≤ m ∧ 0 < u ∧ u<v ∧
       ∀ t : ℝ, f.eval (exp t)=exp (m*t)*(A+B*exp (u*t)+C*exp (v*t)) := by
  classical
  obtain ⟨T,inc,hc⟩ := Infinite.exists_superset_card_eq f.support 3 hf
  let o := T.orderIsoOfFin hc
  let q (i : Fin 3) : ℕ := (o i).val
  let n (i : Fin 3) : ℝ := (q i : ℝ)
  have mono {i j : Fin 3} (lt : i<j) : n i < n j := by
    change (q i : ℝ) < (q j : ℝ)
    exact Nat.cast_lt.mpr (show q i < q j from o.strictMono lt)
  have get (t : ℝ) : f.eval (exp t)=∑ i : Fin 3, f.coeff (q i)*exp (n i*t) := by
    let w (i : ℕ) := f.coeff i*(exp t)^i
    calc
      _ = ∑ i ∈ f.support, w i := by rw [Polynomial.eval_eq_sum];rfl
      _ = ∑ i ∈ T, w i := Finset.sum_subset inc (fun i _ hi => by simp [w,Polynomial.notMem_support_iff.mp hi])
      _ = ∑ i : T, w i.val := (Finset.sum_coe_sort T w).symm
      _ = ∑ i : Fin 3, w (q i) := (o.toEquiv.sum_comp (fun i => w i.val)).symm
      _ = _ := by simp only [w,n,exp_nat_mul]
  refine ⟨n 0,n 1-n 0,n 2-n 0,f.coeff (q 0),f.coeff (q 1),f.coeff (q 2),
    Nat.cast_nonneg _,sub_pos.mpr (mono (by decide)),sub_lt_sub_right (mono (by decide)) _,?_⟩
  intro t
  rw [get]
  simp [Fin.sum_univ_succ,sub_mul,exp_sub]
  field_simp
  <;> ring

theorem general_polynomial_from_cube
    (cube : ∀ d z y l : ℝ, d ∈ Set.Ioo 0 1 → z ∈ Set.Ioo 0 1 →
        y ∈ Set.Ioo 0 1 → l ∈ Set.Ioo 0 1 → inChart d z y l)
    (f g : Polynomial ℝ) (hf : f.support.card ≤ 3) (hg : g.support.card ≤ 3)
    (nz : 1+f*g ≠ 0) :
    ¬ ∃ x : Fin 9 → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧ ∀ i, (1+f*g).eval (x i)=0 := by
  obtain ⟨m,a,c,A,B,C,hm,ha,hac,ff⟩ := three_terms f hf
  obtain ⟨n,u,v,D,E,F,hn,hu,huv,gg⟩ := three_terms g hg
  let R := rawProduct (m+n) u v a (c-a) A B C D E F
  have same (t : ℝ) : R t=(1+f*g).eval (exp t) := by
    simp only [Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,ff,gg,R,rawProduct]
    rw [show a+(c-a)=c by ring,add_mul,exp_add]
    ring
  have nz' : ∃ t, R t ≠ 0 := by
    by_contra! h
    apply nz
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioi_infinite (0:ℝ)).mono
    intro x hx
    change 0 < x at hx
    change (1+f*g).eval x=0
    simpa only [same,exp_log hx] using h (log x)
  have bound := general_product_from_cube cube (add_nonneg hm hn) hu huv ha (sub_pos.mpr hac) nz'
  rintro ⟨x,hx,hp,hz⟩
  apply bound
  refine ⟨fun i => log (x i),fun i j h => log_lt_log (hp i) (hx h),?_⟩
  intro i
  change R (log (x i))=0
  rw [same,exp_log (hp i)];exact hz i
#print axioms general_polynomial_from_cube

def sLa (u v a : ℝ) := (a+v)*(a-u)*(a+v-u)^2
def sRa (u v a : ℝ) := (a+u)*(a-v)*(a+u-v)^2
def sLb (u v a b : ℝ) := (a+b-u)*(a+b+v-u)*(b-v)*(b+u-v)
def sRb (u v a b : ℝ) := (a+b-v)*(a+b+u-v)*(b-u)*(b+v-u)
def SL (u v a b : ℝ) := sLa u v a*sLb u v a b
def SR (u v a b : ℝ) := sRa u v a*sRb u v a b
def firstDelta (s u v a b : ℝ) :=
    (s+u)*(s+a+v)*SL u v a b-(s+v)*(s+a+u)*SR u v a b

theorem factored_one (s u v a b : ℝ) : testOne s u v a b = a^2*(a+b)*b*firstDelta s u v a b := by
  have la : up u v a v*down u v a u=a^2*sLa u v a := by unfold up down sLa;ring
  have ra : up u v a u*down u v a v=a^2*sRa u v a := by unfold up down sRa;ring
  have w (e : ℝ) : weight s u v a b e=(s+e)*down u v (a+b) e := by unfold weight down;ring
  have x (e : ℝ) : weight s u v a b (a+e)=(s+a+e)*down u v b e := by unfold weight down;ring
  have lb : down u v (a+b) u*down u v b v=(a+b)*b*sLb u v a b := by unfold down sLb;ring
  have rb : down u v (a+b) v*down u v b u=(a+b)*b*sRb u v a b := by unfold down sRb;ring
  unfold testOne firstDelta SL SR
  dsimp only
  rw [la,ra,x v,x u,w u,w v]
  linear_combination a^2*sLa u v a*(s+u)*(s+a+v)*lb - a^2*sRa u v a*(s+v)*(s+a+u)*rb

set_option maxRecDepth 50000 in
set_option maxHeartbeats 16000000 in
private theorem slope_polys {u w x y : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let v := u+w
    let a := v+x
    let b := v+2*x+y
    let A := SL u v a b
    let B := SR u v a b
    0 ≤ A-B ∧ 0 ≤ 7*(2*x^2*(A-B)+11*(u*(a+v)*A-v*(a+u)*B))+11*x*(u+2*v)*(A-B) := by
  dsimp only
  unfold SL SR sLa sLb sRa sRb
  constructor <;> ring_nf <;> positivity

theorem sharper {s u v a b : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (huv : u ≤ v)
    (hva : v ≤ a) (hvb : 2*a-v ≤ b)
    (bad : testOne s u v a b < 0) : 11*s*(s+(a-v)) < 2*(a-v)^2 := by
  by_contra! hd
  let x := a-v
  let A := SL u v a b
  let B := SR u v a b
  have hx : 0 ≤ x := sub_nonneg.mpr hva
  have hD : 0 ≤ 11*s*(s+x)-2*x^2 := sub_nonneg.mpr hd
  have hS : x ≤ 7*s := by
    by_contra! ha
    have hpos := mul_pos (sub_pos.mpr ha) (show 0 < 2*x+3*s by linarith)
    nlinarith only [hpos,hD,sq_nonneg s]
  have ⟨p,r⟩ := slope_polys hu (sub_nonneg.mpr huv) hx (sub_nonneg.mpr hvb)
  have eV : u+(v-u)=v := by ring
  have eA : v+x=a := by dsimp [x];ring
  have eB : v+2*x+(b-(2*a-v))=b := by dsimp [x];ring
  rw [eV,eA,eB] at p r
  change 0 ≤ A-B at p
  change 0 ≤ 7*(2*x^2*(A-B)+11*(u*(a+v)*A-v*(a+u)*B))+11*x*(u+2*v)*(A-B) at r
  have main : 0 ≤ firstDelta s u v a b := by
    change 0 ≤ (s+u)*(s+a+v)*A-(s+v)*(s+a+u)*B
    have hprod := mul_nonneg hD p
    have extra := mul_nonneg (mul_nonneg (sub_nonneg.mpr hS) (show 0 ≤ u+2*v by linarith)) p
    dsimp [x] at r hprod extra
    nlinarith only [r,hprod,extra]
  rw [factored_one] at bad
  exact bad.not_ge (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)) main)
#print axioms sharper

set_option maxRecDepth 40000 in
set_option maxHeartbeats 10000000 in
private theorem five_u_poly {x y w t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (ht : 0 ≤ t) :
    let u := x+y
    let v := u+w
    0 ≤ firstDelta 0 u v (v+5*x) (v+10*x+t) := by
  dsimp only
  unfold firstDelta SL SR sLa sLb sRa sRb
  ring_nf;positivity

theorem pos_five_u {s u v a b : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (huv : u ≤ v)
    (hg : 0 ≤ a-v) (hb : 2*a-v ≤ b) (hU : a-v ≤ 5*u) :
    0 ≤ testOne s u v a b := by
  have xp : 0 ≤ (a-v)/5 := by linarith
  have zp : 0 ≤ u-(a-v)/5 := by linarith
  have h0 := five_u_poly xp zp (sub_nonneg.mpr huv) (sub_nonneg.mpr hb)
  have zero : 0 ≤ firstDelta 0 u v a b := by
    dsimp only at h0
    ring_nf at h0 ⊢
    exact h0
  have ⟨d,_⟩ := slope_polys hu (sub_nonneg.mpr huv) hg (sub_nonneg.mpr hb)
  rw [show u+(v-u)=v by ring,show v+(a-v)=a by ring,show v+2*(a-v)+(b-(2*a-v))=b by ring] at d
  have p := mul_nonneg (mul_nonneg hs (show 0 ≤ s+a+u+v by linarith)) d
  have val : 0 ≤ firstDelta s u v a b := by
    unfold firstDelta at zero ⊢
    nlinarith only [p,zero]
  rw [factored_one]
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)) val
#print axioms pos_five_u


end GapAudit



namespace ConeCert
structure Ops (α : Type) where
  zero : α
  lit : ℤ → α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  good : α → Bool
structure Laws {α : Type} (o : Ops α) (v : α → ℝ) : Prop where
  z : v (o.zero)=0
  lit : ∀ i, v (o.lit i)=(i:ℝ)
  add : ∀ a b, v (o.add a b)=v a+v b
  neg : ∀ a, v (o.neg a)= -(v a)
  mul : ∀ a b, v (o.mul a b)=v a*v b
  good : ∀ a, o.good a=true → 0 ≤ v a

def ints : Ops ℤ := ⟨0,id,(·+·),Neg.neg,(·*·),fun x => decide (0 ≤ x)⟩
theorem intLaws : Laws ints (fun x => (x:ℝ)) := by
  constructor
  · simp [ints]
  · simp [ints]
  · simp [ints]
  · simp [ints]
  · simp [ints]
  · intro a h;simpa [ints] using h

def plus {α} (o : Ops α) : List α → List α → List α
  | [],bs => bs
  | as,[] => as
  | a::as,b::bs => o.add a b :: plus o as bs
def times {α} (o : Ops α) (as bs : List α) : List α :=
  match as,bs with
  | [],_ | _,[] => []
  | a::xs, b::ys => plus o ((b::ys).map (o.mul a)) (o.zero :: times o xs (b::ys))
termination_by structural as
def lift {α} (o : Ops α) : Ops (List α) :=
  ⟨[],fun i => [o.lit i],plus o,fun p => p.map o.neg,times o,fun p => p.all o.good⟩
def hor {α} (v : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a::as => v a+x*hor v x as

theorem liftLaws {α} {o : Ops α} {v : α → ℝ} (L : Laws o v) (x : ℝ) (hx : 0 ≤ x) :
    Laws (lift o) (hor v x) := by
  have addH (a b : List α) : hor v x (plus o a b)=hor v x a+hor v x b := by
    induction a generalizing b with
    | nil => simp [plus,hor]
    | cons a as ih => cases b with
      | nil => simp [plus,hor]
      | cons b bs => simp only [plus,hor,L.add,ih];ring
  have scale (a : α) (b : List α) : hor v x (b.map (o.mul a))=v a*hor v x b := by
    induction b with
    | nil => simp [hor]
    | cons b bs ih => simp only [List.map_cons,hor,L.mul,ih];ring
  refine ⟨rfl,?_,addH,?_,?_,?_⟩
  · intro i;simp [lift,hor,L.lit]
  · intro a;change hor v x (a.map o.neg)= -(hor v x a)
    induction a with
    | nil => simp [hor]
    | cons a as ih => simp only [List.map_cons,hor,L.neg,ih];ring
  · intro a b;change hor v x (times o a b)=_
    induction a with
    | nil => cases b <;> simp [times,hor]
    | cons a as ih =>
      cases b with
      | nil => simp [times,hor]
      | cons b bs =>
        rw [times,addH,scale]
        simp only [hor,L.z,zero_add] at ih ⊢
        rw [ih];ring
  · intro a h
    change a.all o.good=true at h
    induction a with
    | nil => simp [hor]
    | cons a as ih =>
      simp only [List.all_cons,Bool.and_eq_true] at h
      exact add_nonneg (L.good _ h.1) (mul_nonneg hx (ih h.2))

inductive T where
  | num (n : ℤ)
  | v0 | v1 | v2 | v3
  | plus (a b : T)
  | neg (a : T)
  | times (a b : T)
deriving Inhabited
instance : OfNat T n := ⟨T.num n⟩
instance : Add T := ⟨T.plus⟩
instance : Neg T := ⟨T.neg⟩
instance : Sub T := ⟨fun x y => x+ -y⟩
instance : Mul T := ⟨T.times⟩

def run {α} (o : Ops α) (x y z w : α) : T → α
 | .num i => o.lit i
 | .v0 => x
 | .v1 => y
 | .v2 => z
 | .v3 => w
 | .plus a b => o.add (run o x y z w a) (run o x y z w b)
 | .neg a => o.neg (run o x y z w a)
 | .times a b => o.mul (run o x y z w a) (run o x y z w b)
def val (x y z w : ℝ) : T → ℝ
 | .num i => i
 | .v0 => x
 | .v1 => y
 | .v2 => z
 | .v3 => w
 | .plus a b => val x y z w a+val x y z w b
 | .neg a => -(val x y z w a)
 | .times a b => val x y z w a*val x y z w b

theorem run_eq {α} {o : Ops α} {v : α → ℝ} (L : Laws o v) (x y z w : α) (e : T) :
    v (run o x y z w e)=val (v x) (v y) (v z) (v w) e := by
  induction e <;> simp_all [run,val,L.lit,L.add,L.neg,L.mul]

abbrev O1 := lift ints
abbrev O2 := lift O1
abbrev O3 := lift O2
abbrev O4 := lift O3
def X : List (List (List (List ℤ))) := [[],[[[1]]]]
def Y : List (List (List (List ℤ))) := [[[],[[1]]]]
def Z : List (List (List (List ℤ))) := [[[[],[1]]]]
def W : List (List (List (List ℤ))) := [[[[0,1]]]]
def check (t : T) := O4.good (run O4 X Y Z W t)

theorem check_sound (e : T) (h : check e=true) (x y z w : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) : 0 ≤ val x y z w e := by
  have L := liftLaws (liftLaws (liftLaws (liftLaws intLaws w hw) z hz) y hy) x hx
  have cert := L.good _ h
  rw [run_eq L] at cert
  simpa [X,Y,Z,W,hor] using cert
#print axioms check_sound
end ConeCert

namespace ConeCert
def triG {R : Type} [Add R] [Sub R] [Mul R] (u v a b : R) : R :=
  let w := v-u
  let c := a+b
  (a+u)*(a+u)*(a-w)*(b-u)*(b+w)*(c+v)*(c+v)*(c+w)*(b+v)*(b+w) -
  (a+v)*(a+v)*(a+w)*(b-v)*(b-w)*(c+u)*(c+u)*(c-w)*(b+u)*(b-w)
def nearG {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 5]
    (alt : Bool) (x y z w : R) : R :=
  let g := 5*(x+y+z)
  let u := if alt then x+y else x
  let v := g*(1+w)*(1+w)
  let t := if alt then 5*x*(1+w) else 5*(x+y)*(1+w)
  triG u v (v+g) (v+g+g+t)

structure Cub (R : Type) where
  c : R
  p : R
  q : R
  r : R

def c1 {R : Type} [Add R] [Sub R] [Mul R] (u v a b : R) : Cub R :=
  let w := v-u
  let c := a+b
  let f := (c-u)*(c+w)*(b+u)*(b+v)*(b-v)*(b-w)
  let n := (a+u+v)*(a-u)*(a-v)
  ⟨v*(a-u)*n*f,u,a,a+v⟩
def c2 {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 0] (u v a b : R) : Cub R :=
  let w := v-u
  let c := a+b
  let f := (c+u)*(c+v)*(b-u)*(b+w)*(b-v)*(b-w)
  let d := a*(a-w)*(a+w)
  ⟨w*a*d*f,0,a+u,a+v⟩
def c3 {R : Type} [Add R] [Sub R] [Mul R] (u v a b : R) : Cub R :=
  let w := v-u
  let c := a+b
  let f := (c-v)*(c-w)*(b-u)*(b+w)*(b+u)*(b+v)
  let n := (a+u+v)*(a-u)*(a-v)
  ⟨u*(a-v)*n*f,v,a+u,a⟩
def mix {R : Type} [Add R] [Mul R] [OfNat R 6] (k : Fin 4) (g : R) (s : Cub R) : R :=
  let p := 6*s.p
  let q := 6*s.q
  let r := 6*s.r
  s.c * (match k with
    | 0 => p*q*r
    | 1 => (p+g)*q*r + p*(q+g)*r + p*q*(r+g)
    | 2 => (p+g)*(q+g)*r + (p+g)*q*(r+g) + p*(q+g)*(r+g)
    | 3 => (p+g)*(q+g)*(r+g))
def control {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 0] [OfNat R 6]
    (k : Fin 4) (u v g b : R) : R :=
  let a := v+g
  mix k g (c1 u v a b) - mix k g (c2 u v a b) - mix k g (c3 u v a b)
def lowG {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 0] [OfNat R 6]
    (i : Fin 4) (u w z t : R) : R :=
  let v := u+w
  let g := v+z
  control i u v g (v+g+g+t)
def farG {R : Type} [Add R] [Sub R] [Mul R] [OfNat R 0] [OfNat R 1] [OfNat R 5] [OfNat R 6]
    (i : Fin 4) (x y z w : R) : R :=
  let g := 5*(x+y)
  let v := g*(1+z)*(1+z)
  control i x v g (v+g+g+g*(1+z+w))

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
theorem cert_nearGfalse : check (nearG false T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_nearGfalse
theorem cert_nearGtrue : check (nearG true T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_nearGtrue
theorem cert_lowG0 : check (lowG 0 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_lowG0
theorem cert_lowG1 : check (lowG 1 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_lowG1
theorem cert_lowG2 : check (lowG 2 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_lowG2
theorem cert_lowG3 : check (lowG 3 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_lowG3
theorem cert_farG0 : check (farG 0 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_farG0
theorem cert_farG1 : check (farG 1 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_farG1
theorem cert_farG2 : check (farG 2 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_farG2
theorem cert_farG3 : check (farG 3 T.v0 T.v1 T.v2 T.v3)=true := by decide +kernel
#print axioms cert_farG3
theorem valA (x y z w : ℝ) (a b : T) : val x y z w (a+b)=val x y z w a+val x y z w b := rfl
theorem valM (x y z w : ℝ) (a b : T) : val x y z w (a*b)=val x y z w a*val x y z w b := rfl
theorem valS (x y z w : ℝ) (a b : T) : val x y z w (a-b)=val x y z w a-val x y z w b := by
  rw [sub_eq_add_neg];rfl
theorem valN (x y z w : ℝ) (n : ℕ) : val x y z w (T.num (n:ℤ))=(n:ℝ) := by simp [val]
theorem val0 (x y z w : ℝ) : val x y z w 0=0 := rfl
theorem val1 (x y z w : ℝ) : val x y z w 1=1 := rfl
theorem val5 (x y z w : ℝ) : val x y z w 5=5 := rfl
theorem val6 (x y z w : ℝ) : val x y z w 6=6 := rfl
theorem Vtri (x y z w : ℝ) (U V A B : T) :
    val x y z w (triG U V A B)=triG (val x y z w U) (val x y z w V) (val x y z w A) (val x y z w B) := by
  simp only [triG,valA,valM,valS]
def cv (x y z w : ℝ) (p : Cub T) : Cub ℝ := ⟨val x y z w p.c,val x y z w p.p,val x y z w p.q,val x y z w p.r⟩
theorem Vc1 (x y z w : ℝ) (U V A B : T) : cv x y z w (c1 U V A B)=c1 (val x y z w U) (val x y z w V) (val x y z w A) (val x y z w B) := by
  simp only [c1,cv,valA,valM,valS]
theorem Vc2 (x y z w : ℝ) (U V A B : T) : cv x y z w (c2 U V A B)=c2 (val x y z w U) (val x y z w V) (val x y z w A) (val x y z w B) := by
  simp only [c2,cv,valA,valM,valS,val0]
theorem Vc3 (x y z w : ℝ) (U V A B : T) : cv x y z w (c3 U V A B)=c3 (val x y z w U) (val x y z w V) (val x y z w A) (val x y z w B) := by
  simp only [c3,cv,valA,valM,valS]
theorem Vmix (x y z w : ℝ) (k : Fin 4) (G : T) (P : Cub T) :
    val x y z w (mix k G P)=mix k (val x y z w G) (cv x y z w P) := by
  fin_cases k <;> simp only [mix,cv,valA,valM,val6]
theorem Vctrl (x y z w : ℝ) (k : Fin 4) (U V G B : T) :
    val x y z w (control k U V G B)=control k (val x y z w U) (val x y z w V) (val x y z w G) (val x y z w B) := by
  simp only [control,valS,Vmix,Vc1,Vc2,Vc3,valA]
theorem Vnear (x y z w : ℝ) (k : Bool) :
    val x y z w (nearG k T.v0 T.v1 T.v2 T.v3)=nearG k x y z w := by
  cases k <;> simp only [nearG,Bool.false_eq_true,if_false,if_true,Vtri,valM,valA,val1,val5] <;> rfl
theorem Vlow (x y z w : ℝ) (k : Fin 4) :
    val x y z w (lowG k T.v0 T.v1 T.v2 T.v3)=lowG k x y z w := by
  simp only [lowG,Vctrl,valA];rfl
theorem Vfar (x y z w : ℝ) (k : Fin 4) :
    val x y z w (farG k T.v0 T.v1 T.v2 T.v3)=farG k x y z w := by
  simp only [farG,Vctrl,valA,valM,val1,val5];rfl
theorem pos_nearG (i : Bool) (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ nearG i x y z w := by
  have d : check (nearG i T.v0 T.v1 T.v2 T.v3)=true := by
    cases i
    · exact cert_nearGfalse
    · exact cert_nearGtrue
  rw [←Vnear x y z w i]
  exact check_sound _ d _ _ _ _ hx hy hz hw
#print axioms pos_nearG
theorem pos_lowG (i : Fin 4) (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ lowG i x y z w := by
  have d : check (lowG i T.v0 T.v1 T.v2 T.v3)=true := by
    fin_cases i
    · exact cert_lowG0
    · exact cert_lowG1
    · exact cert_lowG2
    · exact cert_lowG3
  rw [←Vlow x y z w i]
  exact check_sound _ d _ _ _ _ hx hy hz hw
#print axioms pos_lowG
theorem pos_farG (i : Fin 4) (x y z w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ farG i x y z w := by
  have d : check (farG i T.v0 T.v1 T.v2 T.v3)=true := by
    fin_cases i
    · exact cert_farG0
    · exact cert_farG1
    · exact cert_farG2
    · exact cert_farG3
  rw [←Vfar x y z w i]
  exact check_sound _ d _ _ _ _ hx hy hz hw
#print axioms pos_farG
end ConeCert

namespace GapAudit
open Real ConeCert

def cubEval (s : ℝ) (c : Cub ℝ) := c.c*(s+c.p)*(s+c.q)*(s+c.r)
def total (s u v a b : ℝ) :=
    cubEval s (c1 u v a b) - cubEval s (c2 u v a b) - cubEval s (c3 u v a b)
theorem cubic_mix (s g : ℝ) (c : Cub ℝ) :
    (6*g)^3*cubEval s c =
      (g-6*s)^3*mix 0 g c+(g-6*s)^2*(6*s)*mix 1 g c+
      (g-6*s)*(6*s)^2*mix 2 g c+(6*s)^3*mix 3 g c := by
  rcases c with ⟨c,p,q,r⟩
  simp [cubEval,mix]
  ring

theorem total_of_controls {s u v g b : ℝ} (hg : 0 < g) (hs : 0 ≤ s) (hs' : 6*s ≤ g)
    (valid : ∀ i, 0 ≤ control i u v g b) : 0 ≤ total s u v (v+g) b := by
  let A := c1 u v (v+g) b
  let B := c2 u v (v+g) b
  let C := c3 u v (v+g) b
  have hs0 : 0 ≤ g-6*s := sub_nonneg.mpr hs'
  have h6 : 0 ≤ 6*s := by positivity
  have h (i : Fin 4) : 0 ≤ mix i g A - mix i g B - mix i g C := valid i
  have z0 := mul_nonneg (pow_nonneg hs0 3) (h 0)
  have z1 := mul_nonneg (mul_nonneg (sq_nonneg (g-6*s)) h6) (h 1)
  have z2 := mul_nonneg (mul_nonneg hs0 (sq_nonneg (6*s))) (h 2)
  have z3 := mul_nonneg (pow_nonneg h6 3) (h 3)
  have combo : 0 ≤ (6*g)^3*(cubEval s A-cubEval s B-cubEval s C) := by
    rw [mul_sub,mul_sub,cubic_mix s g A,cubic_mix s g B,cubic_mix s g C]
    linarith only [z0,z1,z2,z3]
  exact nonneg_of_mul_nonneg_right combo (pow_pos (by positivity : 0 < 6*g) 3)

def commonTwo (s u v a b : ℝ) :=
    (a*(a+u)*(a+v))*((a+b)*b)^2*((s+u)*(a+b-u)*(a+b+(v-u)))

theorem factor_two (s u v a b : ℝ) (hv : v≠0) :
    v*testTwo s u v a b (u/v) = commonTwo s u v a b*total s u v a b := by
  let w := v-u
  let c := a+b
  have n : lowerN a u v = (a*(a+u)*(a+v))*((a+u+v)*(a-u)*(a-v)) := by
    unfold lowerN factorN;ring
  have d : lowerD a u v = (a*(a+u)*(a+v))*(a*(a-w)*(a+w)) := by dsimp [lowerD,up,w];ring
  have w0 : weight s u v a b 0 = s*c*(c+u)*(c+v) := by dsimp [weight,c];ring
  have w1 : weight s u v a b u = (s+u)*(c-u)*c*(c+w) := by dsimp [weight,c,w];ring
  have w2 : weight s u v a b v = (s+v)*(c-v)*(c-w)*c := by dsimp [weight,c,w];ring
  have w3 : weight s u v a b a = (s+a)*b*(b+u)*(b+v) := by dsimp [weight];ring
  have w4 : weight s u v a b (a+u) = (s+(a+u))*(b-u)*b*(b+w) := by dsimp [weight,w];ring
  have w5 : weight s u v a b (a+v) = (s+(a+v))*(b-v)*(b-w)*b := by dsimp [weight,w];ring
  have fr (p q r : ℝ) : v*(p-(1-u/v)*q-(u/v)*r)=v*p-w*q-u*r := by dsimp [w];field_simp
  unfold testTwo
  dsimp only
  simp only [mul_assoc] at fr ⊢
  rw [fr,w0,w1,w2,w3,w4,w5,n,d]
  unfold commonTwo total cubEval c1 c2 c3
  dsimp only
  change _=(a*(a+u)*(a+v))*(c*b)^2*((s+u)*(c-u)*(c+w))*_
  simp only [show v-u=w by rfl,show a+b=c by rfl]
  conv_rhs => rw [mul_sub]; lhs; rw [mul_sub]
  simp only [pow_two,add_zero]
  apply congrArg₂ (·-·)
  · apply congrArg₂ (·-·) <;> ac_rfl
  · ac_rfl

theorem factor_three (u v a b : ℝ) :
    testThree u v a b = a*(a+b)*b^2*triG u v a b := by
  let w := v-u
  let c := a+b
  have mu : (a+u)*midNum u v a b u=(a+u)*(a+u)*a*(a-w)*(b-u)*b*(b+w) := by
    dsimp [midNum,up,down,w];ring
  have mv : (a+v)*midNum u v a b v=(a+v)*(a+v)*(a+w)*a*(b-v)*(b-w)*b := by
    dsimp [midNum,up,down,w];ring
  have tu : (a+b+u)*topNum u v a b u=(c+u)*(c+u)*c*(c-w)*(b+u)*b*(b-w) := by
    dsimp [topNum,up,w,c];ring
  have tv : (a+b+v)*topNum u v a b v=(c+v)*(c+v)*(c+w)*c*(b+v)*(b+w)*b := by
    dsimp [topNum,up,w,c];ring
  unfold testThree
  rw [mu,mv,tu,tv]
  unfold triG
  dsimp only
  simp only [show v-u=w by rfl,show a+b=c by rfl]
  conv_rhs => rw [mul_sub]
  simp only [pow_two]
  apply congrArg₂ (·-·) <;> ac_rfl
end GapAudit
namespace GapAudit
open Real ConeCert
section
variable (liftLow : ∀ (i : Fin 4) (x y z w : ℝ), 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ w → 0 ≤ lowG i x y z w)
    (liftNear : ∀ (i : Bool) (x y z w : ℝ), 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ w → 0 ≤ nearG i x y z w)
    (liftFar : ∀ (i : Fin 4) (x y z w : ℝ), 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ w → 0 ≤ farG i x y z w)
include liftLow liftNear liftFar in
theorem certify_exponents {s u v a b : ℝ} (hs : 0 ≤ s) (hu : 0 < u) (huv : u<v) (hva : v<a)
    (hb : 2*a-v≤b) (sg : 6*s≤a-v) (ug : 5*u≤a-v) :
    0≤testTwo s u v a b (u/v) ∨ 0≤testThree u v a b := by
  let g := a-v
  let t := b-(a+g)
  have hg : 0<g := sub_pos.mpr hva
  have hv := hu.trans huv
  have ha := hv.trans hva
  have hb0 : 0<b := by linarith
  have ht : 0≤t := by dsimp [t,g];linarith
  have ea : v+g=a := by dsimp [g];ring
  have eb : a+g+t=b := by dsimp [t];ring
  have E (ci : ∀ i,0≤control i u v g b) : 0≤testTwo s u v a b (u/v) := by
    have tc := total_of_controls hg hs sg ci
    rw [ea] at tc
    have pc : 0 ≤ commonTwo s u v a b := by
      have k1 : 0 ≤ a+b-u := by linarith
      have k2 : 0 ≤ v-u := sub_nonneg.mpr huv.le
      unfold commonTwo
      positivity
    have res := mul_nonneg pc tc
    rw [←factor_two _ _ _ _ _ hv.ne'] at res
    exact nonneg_of_mul_nonneg_right res hv
  have E3 (p : 0≤triG u v a b) : 0≤testThree u v a b := by
    rw [factor_three]
    positivity
  by_cases low : v≤g
  · left;apply E;intro i
    have h := liftLow i u (v-u) (g-v) t hu.le (sub_nonneg.mpr huv.le) (sub_nonneg.mpr low) ht
    change 0≤control i _ _ _ _ at h
    simpa only [lowG,show u+(v-u)=v by ring,show v+(g-v)=g by ring,ea,eb] using h
  have gv : g≤v := (le_of_not_ge low)
  let q := Real.sqrt (v/g)
  have qpos : 0<q := Real.sqrt_pos.2 (div_pos hv hg)
  have sq : q^2=v/g := Real.sq_sqrt (div_nonneg hv.le hg.le)
  have hq : 1≤q := by
    by_contra! h
    have := (one_le_div hg).mpr gv
    nlinarith only [sq,this,mul_pos (sub_pos.mpr h) (show 0<1+q by linarith)]
  have vg : g*q*q=v := by rw [mul_assoc,←pow_two,sq];field_simp
  have oneZ : 1+(q-1)=q := by ring
  rcases le_total t (g*q) with small|big
  · right;apply E3
    let L := t/(5*q)
    have L0 : 0≤L := div_nonneg ht (by positivity)
    have Lg : L≤g/5 := (div_le_iff₀ (by positivity : 0<5*q)).mpr (by linarith)
    have uP : u≤g/5 := by dsimp [g];linarith
    have T : 5*L*q=t := by dsimp [L];field_simp
    rcases le_total u L with hUL|hLU
    · have h := liftNear false u (L-u) (g/5-L) (q-1) hu.le (sub_nonneg.mpr hUL) (sub_nonneg.mpr Lg) (sub_nonneg.mpr hq)
      change 0≤triG u _ _ _ at h
      have h1 : u+(L-u)=L := by ring
      have h2 : 5*(L+(g/5-L))=g := by ring
      simpa only [Bool.false_eq_true,if_false,if_true,h1,h2,oneZ,vg,ea,T,eb] using h
    · have h := liftNear true L (u-L) (g/5-u) (q-1) L0 (sub_nonneg.mpr hLU) (sub_nonneg.mpr uP) (sub_nonneg.mpr hq)
      change 0≤triG (L+(u-L)) _ _ _ at h
      have h1 : L+(u-L)=u := by ring
      have h2 : 5*(u+(g/5-u))=g := by ring
      simpa only [Bool.false_eq_true,if_false,if_true,h1,h2,oneZ,vg,ea,T,eb] using h
  · left;apply E;intro i
    have tail : 0≤t/g-q := sub_nonneg.mpr ((le_div_iff₀ hg).mpr (by linarith))
    have uP : u≤g/5 := by dsimp [g];linarith
    have h := liftFar i u (g/5-u) (q-1) (t/g-q) hu.le (sub_nonneg.mpr uP) (sub_nonneg.mpr hq) tail
    change 0≤control i u _ _ _ at h
    have h1 : 5*(u+(g/5-u))=g := by ring
    have h2 : g*(q+(t/g-q))=t := by field_simp <;> ring
    simpa only [h1,oneZ,vg,ea,h2,eb] using h
end
end GapAudit
namespace GapAudit
open Real ConeCert
theorem cube_positive (d z y l : ℝ) (hd : d∈Set.Ioo 0 1) (hz : z∈Set.Ioo 0 1) (hy : y∈Set.Ioo 0 1) (hl : l∈Set.Ioo 0 1) : inChart d z y l := by
  let a := 2*(1-l)
  let v := a*(1-d)
  let u := z*v
  let b := 2*(1+d)
  let s := d*y*(1-l)
  have ha : 0<a := mul_pos (by norm_num) (sub_pos.mpr hl.2)
  have hv : 0<v := mul_pos ha (sub_pos.mpr hd.2)
  have hu : 0<u := mul_pos hz.1 hv
  have uv : u<v := by dsimp [u];exact mul_lt_of_lt_one_left hv hz.2
  have va : v<a := by dsimp [v];exact mul_lt_of_lt_one_right ha (by linarith [hd.1])
  have hs : 0 ≤ s := (mul_pos (mul_pos hd.1 hy.1) (sub_pos.mpr hl.2)).le
  have hb : 2*a-v ≤ b := by dsimp [a,v,b];nlinarith only [hl.1,mul_nonneg hd.1.le hl.1.le]
  change 0 ≤ testOne s u v a b ∨ 0 ≤ testTwo s u v a b z ∨ 0 ≤ testThree u v a b
  by_cases good : 0 ≤ testOne s u v a b
  · exact Or.inl good
  have bad := lt_of_not_ge good
  have hg : 0 ≤ a-v := sub_nonneg.mpr va.le
  have q := sharper hs hu.le uv.le va.le hb bad
  have sg : 6*s ≤ a-v := by
    by_contra! low
    nlinarith only [mul_nonneg (sub_nonneg.mpr low.le) (show 0 ≤ s+2*(a-v) by linarith),sq_nonneg s,q]
  have ug : 5*u ≤ a-v := by
    by_contra! low
    exact good (pos_five_u hs hu.le uv.le hg hb low.le)
  have c := certify_exponents pos_lowG pos_nearG pos_farG hs hu uv va hb sg ug
  have rz : u/v=z := by dsimp [u];field_simp
  rw [rz] at c
  exact Or.inr c
#print axioms cube_positive
theorem eight_distinct_positive (f g : Polynomial ℝ) (hf : f.support.card  ≤  3)
    (hg : g.support.card  ≤  3) (nz : 1+f*g ≠ 0) :
    ¬ ∃ x : Fin 9 → ℝ, StrictMono x ∧ (∀ i,0<x i) ∧ ∀ i,(1+f*g).eval (x i)=0 :=
  general_polynomial_from_cube cube_positive f g hf hg nz
#print axioms eight_distinct_positive

theorem positive_root_count (f g : Polynomial ℝ) (hf : f.support.card  ≤  3)
    (hg : g.support.card  ≤  3) (nz : 1+f*g ≠ 0) :
    (((1+f*g).roots.toFinset).filter (fun x => 0<x)).card  ≤  8 := by
  classical
  by_contra! many
  let S := ((1+f*g).roots.toFinset).filter (fun x => 0<x)
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq (s:=S) (show 9 ≤ S.card from many)
  let e := T.orderIsoOfFin hcard
  apply eight_distinct_positive f g hf hg nz
  refine ⟨fun i => (e i).val, fun i j h => e.strictMono h, ?_, ?_⟩
  · intro i
    exact (Finset.mem_filter.mp (hT (e i).property)).2
  · intro i
    have h := (Finset.mem_filter.mp (hT (e i).property)).1
    exact Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp h)
#print axioms positive_root_count
end GapAudit
