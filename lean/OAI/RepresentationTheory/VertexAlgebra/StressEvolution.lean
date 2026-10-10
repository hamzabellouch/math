import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SymmetricWeakCommute

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
lemma term_continuous {K : ℝ → A} (hK : Continuous K) (n : ℕ) : Continuous (term K n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact continuous_iff_continuousAt.mpr fun t =>
      (intervalIntegral.integral_hasDerivAt_right ((hK.mul ih).intervalIntegrable 0 t)
       (hK.mul ih).stronglyMeasurable.stronglyMeasurableAtFilter (hK.mul ih).continuousAt).continuousAt

lemma term_derivative {K : ℝ → A} (hK : Continuous K) (n : ℕ) (t : ℝ) :
    HasDerivAt (term K (n+1)) (K t*term K n t) t := by
  have hc := hK.mul (term_continuous hK n)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

variable [NormOneClass A]

lemma term_bound {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (n : ℕ) (t : ℝ) :
    ‖term K n t‖ ≤ (M*|t|)^n/(n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simp [term]
  | succ n ih =>
    let g (s : ℝ) := (M^(n+1)/(n.factorial : ℝ))*|s|^n
    have hi : IntervalIntegrable g volume 0 t :=
      (continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t
    have he (s : ℝ) : ‖K s*term K n s‖ ≤ g s := by
      calc
        _ ≤ ‖K s‖*‖term K n s‖ := norm_mul_le _ _
        _ ≤ M*((M*|s|)^n/(n.factorial : ℝ)) := mul_le_mul (hb s) (ih s) (norm_nonneg _) hM
        _ = g s := by dsimp [g]; rw [mul_pow,pow_succ]; ring
    calc
      ‖term K (n+1) t‖ ≤ ∫ s in Ι (0:ℝ) t, ‖K s*term K n s‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Ι (0:ℝ) t, g s := integral_mono_ae
        ((hK.mul (term_continuous hK n)).intervalIntegrable 0 t).norm.def'
        hi.def' (Filter.Eventually.of_forall he)
      _ = (M*|t|)^(n+1)/((n+1).factorial : ℝ) := by
        dsimp only [g]
        rw [integral_const_mul]
        have hx := integral_pow_abs_sub_uIoc (a := (0:ℝ)) (b := t) (n := n)
        simp only [sub_zero] at hx
        rw [hx,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow]
        field_simp

lemma term_summable {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) : Summable (fun n => term K n t) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial (M*|t|)) (fun n => term_bound hK hM hb n t)

def evolution (K : ℝ → A) (t : ℝ) : A := ∑' n, term K n t

omit [CompleteSpace A] [NormOneClass A] in
lemma evolution_zero (K : ℝ → A) : evolution K 0 = 1 := by
  rw [evolution,tsum_eq_single 0]
  · rfl
  · intro n hn
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [term]

lemma evolution_derivative {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) :
    HasDerivAt (evolution K) (K t*evolution K t) t := by
  let R := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  let u (n : ℕ) := M*((M*R)^n/(n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial (M*R)).mul_left M
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n s _ => term_derivative hK n s)
    (fun n s (hs : s ∈ Ioo (-R) R) => by
      calc
        ‖K s*term K n s‖ ≤ ‖K s‖*‖term K n s‖ := norm_mul_le _ _
        _ ≤ M*((M*|s|)^n/(n.factorial : ℝ)) := mul_le_mul (hb s) (term_bound hK hM hb n s) (norm_nonneg _) hM
        _ ≤ u n := by
          dsimp [u]
          gcongr
          exact (abs_lt.mpr hs).le)
    (show (0:ℝ) ∈ Ioo (-R) R from ⟨neg_neg_of_pos hR,hR⟩)
    (by simp only [term,intervalIntegral.integral_same]; exact summable_zero)
    (show t ∈ Ioo (-R) R by dsimp [R]; constructor <;> linarith [le_abs_self t,neg_abs_le t])
  have he (s : ℝ) : evolution K s = 1+∑' n,term K (n+1) s := by
    rw [evolution,(term_summable hK hM hb s).tsum_eq_zero_add]
    rfl
  have hd' := hd.const_add (1:A)
  convert hd' using 1 <;> first | rfl | exact funext he | exact (Summable.tsum_mul_left (K t) (term_summable hK hM hb t)).symm
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_growth {f f' : ℝ → E} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) (t : ℝ) :
    ‖f t‖ ≤ ‖f 0‖*Real.exp (C*|t|) := by
  have hp {g g' : ℝ → E} (hg : ∀ t, HasDerivAt g (g' t) t)
      (hgb : ∀ t, ‖g' t‖ ≤ C*‖g t‖) {s : ℝ} (hs : 0 ≤ s) :
      ‖g s‖ ≤ ‖g 0‖*Real.exp (C*s) := by
    have hc : Continuous g := continuous_iff_continuousAt.mpr (fun r => (hg r).continuousAt)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) hc.continuousOn
      (fun r _ => (hg r).hasDerivWithinAt) (le_refl ‖g 0‖)
      (fun r _ => by simpa only [add_zero] using hgb r) s (show s ∈ Set.Icc 0 s from ⟨hs,le_rfl⟩)
    simpa only [gronwallBound_ε0,sub_zero] using h
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hp hf hb ht
  · have hn : 0 ≤ -t := by linarith
    have hd (s : ℝ) : HasDerivAt (fun r => f (-r)) (-f' (-s)) s := by
      simpa only [neg_one_smul,Function.comp_def] using (hf (-s)).scomp s (hasDerivAt_neg s)
    have hb' (s : ℝ) : ‖-f' (-s)‖ ≤ C*‖f (-s)‖ := by simpa only [norm_neg] using hb (-s)
    simpa only [neg_neg,neg_zero,abs_of_neg (lt_of_not_ge ht)] using hp hd hb' hn

lemma zero_of_derivative_bound {f f' : ℝ → E} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖)
    (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [h0,norm_zero,zero_mul] using norm_growth hf hb t
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
  [StarRing A] [NormedStarGroup A] [StarModule ℝ A]

lemma evolution_unitary {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    star (evolution K t)*evolution K t = 1 ∧ evolution K t*star (evolution K t) = 1 := by
  have hd := evolution_derivative hK hM hb
  have hleft (s : ℝ) : HasDerivAt (fun r => star (evolution K r)*evolution K r) 0 s := by
    convert (hd s).star.mul (hd s) using 1
    rw [star_mul,hk]
    noncomm_ring
  have hl := is_const_of_deriv_eq_zero (fun s => (hleft s).differentiableAt)
    (fun s => (hleft s).deriv) t 0
  simp only [evolution_zero,star_one,mul_one] at hl
  refine ⟨hl,?_⟩
  let z (s : ℝ) := evolution K s*star (evolution K s)-1
  let z' (s : ℝ) := K s*z s-z s*K s
  have hz (s : ℝ) : HasDerivAt z (z' s) s := by
    convert ((hd s).mul (hd s).star).sub_const (1:A) using 1
    dsimp [z,z']
    rw [star_mul,hk]
    noncomm_ring
  have hzb (s : ℝ) : ‖z' s‖ ≤ (2*M)*‖z s‖ := by
    calc
      _ ≤ ‖K s*z s‖+‖z s*K s‖ := norm_sub_le _ _
      _ ≤ ‖K s‖*‖z s‖+‖z s‖*‖K s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M*‖z s‖+‖z s‖*M := by gcongr <;> exact hb s
      _ = _ := by ring
  have hzero := zero_of_derivative_bound hz hzb (by simp [z,evolution_zero]) t
  exact sub_eq_zero.mp hzero
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_mem_unitary {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    evolution K t ∈ unitary (H →L[ℂ] H) := evolution_unitary hK hM hb hk t

lemma evolution_norm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) (x : H) :
    ‖evolution K t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_mem_unitary hK hM hb hk t) x

lemma evolution_star_norm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) (x : H) :
    ‖star (evolution K t) x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (evolution_mem_unitary hK hM hb hk t)) x

lemma evolution_apply_derivative {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (t : ℝ) (x : H) :
    HasDerivAt (fun s => evolution K s x) (K t (evolution K t x)) t :=
  ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (evolution_derivative hK hM hb t)

 

lemma evolution_energy_bound {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) (x : H) :
    ‖S (evolution K t x)‖ ≤ Real.exp (D*|t|)*‖S x‖ := by
  let q (s : ℝ) := star (evolution K s) (S (evolution K s x))
  let q' (s : ℝ) := star (evolution K s) (G s (S (evolution K s x)))
  have hd := evolution_derivative hK hM hb
  have hq (s : ℝ) : HasDerivAt q (q' s) s := by
    have hh := (((hd s).star.mul_const S).mul (hd s))
    have he : (star (K s*evolution K s)*S)*evolution K s +
        (star (evolution K s)*S)*(K s*evolution K s) =
        star (evolution K s)*(G s*S)*evolution K s := by
      rw [star_mul,hk,← hg]
      noncomm_ring
    rw [he] at hh
    exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hh
  have hqb (s : ℝ) : ‖q' s‖ ≤ D*‖q s‖ := by
    dsimp [q,q']
    rw [evolution_star_norm hK hM hb hk,evolution_star_norm hK hM hb hk]
    exact (G s).le_of_opNorm_le (hG s) _
  have hh := norm_growth hq hqb t
  dsimp [q] at hh
  rw [evolution_star_norm hK hM hb hk,evolution_zero] at hh
  simpa only [star_one,one_apply_eq_self,mul_comm] using hh

 

lemma duhamel_bound {K L : ℝ → H →L[ℂ] H} (hK : Continuous K) (hL : Continuous L)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : ∀ t, ‖K t‖ ≤ M) (hc : ∀ t, ‖L t‖ ≤ N)
    (hk : ∀ t, star (K t) = -K t)
    (t : ℝ) (x : H) {δ : ℝ}
    (hδ : ∀ s ∈ uIcc (0:ℝ) t, ‖(L s-K s) (evolution L s x)‖ ≤ δ) :
    ‖evolution L t x-evolution K t x‖ ≤ δ*|t| := by
  let q (s : ℝ) := star (evolution K s) (evolution L s x)
  let q' (s : ℝ) := star (evolution K s) ((L s-K s) (evolution L s x))
  have hq (s : ℝ) : HasDerivAt q (q' s) s := by
    have hh := (evolution_derivative hK hM hb s).star.mul (evolution_derivative hL hN hc s)
    have he : star (K s*evolution K s)*evolution L s +
        star (evolution K s)*(L s*evolution L s) =
        star (evolution K s)*(L s-K s)*evolution L s := by
      rw [star_mul,hk]
      noncomm_ring
    rw [he] at hh
    exact ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hh
  have hh := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hq s).hasDerivWithinAt)
    (fun s hs => by simpa only [q',evolution_star_norm hK hM hb hk] using hδ s hs)
    (left_mem_uIcc) (right_mem_uIcc)
  have he : q t-q 0 = star (evolution K t) (evolution L t x-evolution K t x) := by
    dsimp [q]
    rw [evolution_zero,evolution_zero,star_one,one_apply_eq_self,
      one_apply_eq_self,map_sub]
    have hunit := congrArg (fun T : H →L[ℂ] H => T x) (evolution_unitary hK hM hb hk t).1
    change star (evolution K t) (evolution K t x) = x at hunit
    rw [hunit]
  rw [he,evolution_star_norm hK hM hb hk] at hh
  simpa only [sub_zero,Real.norm_eq_abs] using hh
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma linear_ode_unique {K f g : ℝ → A} {M : ℝ} (hb : ∀ t, ‖K t‖ ≤ M)
    (hf : ∀ t, HasDerivAt f (K t*f t) t) (hg : ∀ t, HasDerivAt g (K t*g t) t)
    (h0 : f 0 = g 0) (t : ℝ) : f t = g t := by
  have hd (s : ℝ) : HasDerivAt (fun r => f r-g r) (K s*(f s-g s)) s := by
    rw [mul_sub]
    exact (hf s).sub (hg s)
  have hm (s : ℝ) : ‖K s*(f s-g s)‖ ≤ M*‖f s-g s‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb s) (norm_nonneg _))
  exact sub_eq_zero.mp (zero_of_derivative_bound hd hm (sub_eq_zero.mpr h0) t)

variable [CompleteSpace A] [NormOneClass A] [StarRing A] [NormedStarGroup A] [StarModule ℝ A]

lemma evolution_reverse {K : ℝ → A} (hK : Continuous K) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t s : ℝ) :
    evolution (fun r => -K (t-r)) s = evolution K (t-s)*star (evolution K t) := by
  have hKr : Continuous (fun r => -K (t-r)) := (hK.comp (continuous_const.sub continuous_id)).neg
  have hbr (r : ℝ) : ‖-K (t-r)‖ ≤ M := by simpa only [norm_neg] using hb (t-r)
  have hr (r : ℝ) : HasDerivAt (fun q => evolution K (t-q)*star (evolution K t))
      (-K (t-r)*(evolution K (t-r)*star (evolution K t))) r := by
    have hh := ((evolution_derivative hK hM hb (t-r)).scomp r
      ((hasDerivAt_id r).const_sub t)).mul_const (star (evolution K t))
    simpa only [Function.comp_def,neg_one_smul,neg_mul,mul_assoc] using hh
  apply linear_ode_unique hbr (evolution_derivative hKr hM hbr) hr _ s
  rw [evolution_zero,sub_zero]
  exact (evolution_unitary hK hM hb hk t).2.symm
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_star_energy_bound {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) (x : H) :
    ‖S (star (evolution K t) x)‖ ≤ Real.exp (D*|t|)*‖S x‖ := by
  have hKr : Continuous (fun r => -K (t-r)) := (hK.comp (continuous_const.sub continuous_id)).neg
  have hbr (r : ℝ) : ‖-K (t-r)‖ ≤ M := by simpa only [norm_neg] using hb (t-r)
  have hkr (r : ℝ) : star (-K (t-r)) = -(-K (t-r)) := by rw [star_neg,hk]
  have hgr (r : ℝ) : S*(-K (t-r))-(-K (t-r))*S = (-G (t-r))*S := by
    calc
      _ = -(S*K (t-r)-K (t-r)*S) := by noncomm_ring
      _ = _ := by rw [hg,neg_mul]
  have hGr (r : ℝ) : ‖-G (t-r)‖ ≤ D := by simpa only [norm_neg] using hG (t-r)
  have h := evolution_energy_bound hKr hM hbr hkr S (fun r => -G (t-r)) hgr hGr t x
  rw [evolution_reverse hK hM hb hk,sub_self,evolution_zero,one_mul] at h
  exact h

 

lemma evolution_regularizer_factor {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M D : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*K t-K t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (t : ℝ) :
    ∃ B : H →L[ℂ] H, (evolution K t).comp S = S.comp B ∧ ‖B‖ ≤ Real.exp (D*|t|) := by
  let L := (S.comp (star (evolution K t))).toLinearMap
  let Q := L.extendOfNorm S.toLinearMap
  have hb' (x : H) : ‖L x‖ ≤ Real.exp (D*|t|)*‖S.toLinearMap x‖ :=
    evolution_star_energy_bound hK hM hb hk S G hg hG t x
  have hQ : Q.comp S = S.comp (star (evolution K t)) := by
    ext x
    exact L.extendOfNorm_eq hSd ⟨_,hb'⟩ x
  have hQa : S.comp Q.adjoint = (evolution K t).comp S := by
    have h := congrArg ContinuousLinearMap.adjoint hQ
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h
  refine ⟨Q.adjoint,hQa.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact L.opNorm_extendOfNorm_le hSd (Real.exp_pos _).le hb'
end StronglyRationalVOA.TimeOrdered

open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

lemma evolution_opNorm {K : ℝ → H →L[ℂ] H} (hK : Continuous K) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t, ‖K t‖ ≤ M) (hk : ∀ t, star (K t) = -K t) (t : ℝ) :
    ‖evolution K t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [evolution_norm hK hM hb hk,one_mul]

lemma evolution_difference_regularized
    {K L : ℝ → H →L[ℂ] H} (hK : Continuous K) (hL : Continuous L)
    {M N D : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : ∀ t, ‖K t‖ ≤ M) (hc : ∀ t, ‖L t‖ ≤ N)
    (hk : ∀ t, star (K t) = -K t) (hl : ∀ t, star (L t) = -L t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℝ → H →L[ℂ] H) (hg : ∀ t, S*L t-L t*S = G t*S)
    (hG : ∀ t, ‖G t‖ ≤ D) (hD : 0 ≤ D)
    {δ : ℝ} (hδ : ∀ t, ‖(L t-K t)*S‖ ≤ δ) (t : ℝ) (x : H) :
    ‖evolution L t (S x)-evolution K t (S x)‖ ≤ δ*Real.exp (D*|t|)*‖x‖*|t| := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  apply duhamel_bound hK hL hM hN hb hc hk
  intro s hs
  obtain ⟨B,hB,hBn⟩ := evolution_regularizer_factor hL hN hc hl S hS hSd G hg hG s
  have he : evolution L s (S x) = S (B x) := congrArg (fun A : H →L[ℂ] H => A x) hB
  rw [he]
  calc
    _ ≤ δ*‖B x‖ := ((L s-K s)*S).le_of_opNorm_le (hδ s) _
    _ ≤ δ*(Real.exp (D*|s|)*‖x‖) := mul_le_mul_of_nonneg_left (B.le_of_opNorm_le hBn x) hd
    _ ≤ δ*(Real.exp (D*|t|)*‖x‖) := by
      have hab : |s| ≤ |t| := by
        rcases mem_uIcc.mp hs with hs' | hs' <;> rw [abs_le] <;> constructor <;>
          nlinarith [neg_abs_le t,le_abs_self t]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hD)) (norm_nonneg x)) hd
    _ = _ := by ring

lemma exists_evolution_limit
    (K : ℕ → ℝ → H →L[ℂ] H) (hK : ∀ n, Continuous (K n))
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hb : ∀ n t, ‖K n t‖ ≤ M n)
    (hk : ∀ n t, star (K n t) = -K n t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℕ → ℝ → H →L[ℂ] H) (hg : ∀ n t, S*K n t-K n t*S = G n t*S)
    {D : ℝ} (hG : ∀ n t, ‖G n t‖ ≤ D) (hD : 0 ≤ D)
    (e : ℕ → ℝ) (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hδ : ∀ n m t, ‖(K n t-K m t)*S‖ ≤ e n+e m) (t : ℝ) :
    ∃ L : H →L[ℂ] H, ∀ x, Tendsto (fun n => evolution (K n) t x) atTop (𝓝 (L x)) := by
  apply StrongLimit.exists_of_dense_core S.range (by change Dense (Set.range S); exact hSd)
    (fun n => evolution (K n) t) (fun n => evolution_opNorm (hK n) (hM n) (hb n) (hk n) t)
  intro x
  obtain ⟨v,hv⟩ := x.property
  have hx : (x : H)=S v := hv.symm
  rw [hx]
  apply cauchySeq_of_le_tendsto_0 (fun n => (2*e n)*Real.exp (D*|t|)*‖v‖*|t|)
  · intro n m N hn hm
    rw [dist_eq_norm]
    calc
      _ ≤ (e n+e m)*Real.exp (D*|t|)*‖v‖*|t| :=
        evolution_difference_regularized (hK m) (hK n) (hM m) (hM n) (hb m) (hb n)
          (hk m) (hk n) S hS hSd (G n) (hg n) (hG n) hD (hδ n m) t v
      _ ≤ _ := by
        gcongr
        have h1 := he hn
        have h2 := he hm
        linarith
  · simpa only [mul_zero,zero_mul] using
      (((he0.const_mul 2).mul_const (Real.exp (D*|t|))).mul_const ‖v‖).mul_const |t|

omit [Nontrivial H] in
lemma unitary_of_strong_and_star_limit (F : ℕ → H →L[ℂ] H)
    (hF : ∀ n, F n ∈ unitary (H →L[ℂ] H)) (L R : H →L[ℂ] H)
    (hl : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (L x)))
    (hr : ∀ x, Tendsto (fun n => star (F n) x) atTop (𝓝 (R x))) :
    L ∈ unitary (H →L[ℂ] H) ∧ star L=R := by
  have hs : star L=R := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have h1 := (hr x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
    have h2 := (tendsto_const_nhds (x := x)).inner (𝕜 := ℂ) (hl y)
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    apply tendsto_nhds_unique h2
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using h1
  have hn (n : ℕ) : ‖F n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (hF n),one_mul]
  have hsn (n : ℕ) : ‖star (F n)‖ ≤ 1 := by simpa only [norm_star] using hn n
  refine ⟨⟨?_,?_⟩,hs⟩
  · ext x
    have h := StrongLimit.mul_tendsto (fun n => star (F n)) F R L hsn hr hl x
    have he (n : ℕ) : star (F n) (F n x)=x := congrArg (fun A : H →L[ℂ] H => A x) (hF n).1
    simp only [he] at h
    change star L (L x)=x
    rw [hs]
    exact tendsto_nhds_unique h tendsto_const_nhds
  · ext x
    have h := StrongLimit.mul_tendsto F (fun n => star (F n)) L R hn hl hr x
    have he (n : ℕ) : F n (star (F n) x)=x := congrArg (fun A : H →L[ℂ] H => A x) (hF n).2
    simp only [he] at h
    change L (star L x)=x
    rw [hs]
    exact tendsto_nhds_unique h tendsto_const_nhds
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

 

lemma exists_unitary_evolution_limit
    (K : ℕ → ℝ → H →L[ℂ] H) (hK : ∀ n, Continuous (K n))
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hb : ∀ n t, ‖K n t‖ ≤ M n)
    (hk : ∀ n t, star (K n t) = -K n t)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (G : ℕ → ℝ → H →L[ℂ] H) (hg : ∀ n t, S*K n t-K n t*S = G n t*S)
    {D : ℝ} (hG : ∀ n t, ‖G n t‖ ≤ D) (hD : 0 ≤ D)
    (e : ℕ → ℝ) (he : Antitone e) (he0 : Tendsto e atTop (𝓝 0))
    (hδ : ∀ n m t, ‖(K n t-K m t)*S‖ ≤ e n+e m) (t : ℝ) :
    ∃ L : H →L[ℂ] H, L ∈ unitary (H →L[ℂ] H) ∧
      (∀ x, Tendsto (fun n => evolution (K n) t x) atTop (𝓝 (L x))) ∧
      (∀ x, Tendsto (fun n => star (evolution (K n) t) x) atTop (𝓝 (star L x))) := by
  obtain ⟨L,hL⟩ := exists_evolution_limit K hK M hM hb hk S hS hSd G hg hG hD e he he0 hδ t
  let Kr (n : ℕ) (s : ℝ) := -K n (t-s)
  let Gr (n : ℕ) (s : ℝ) := -G n (t-s)
  have hKr (n : ℕ) : Continuous (Kr n) := ((hK n).comp (continuous_const.sub continuous_id)).neg
  have hbr (n : ℕ) (s : ℝ) : ‖Kr n s‖ ≤ M n := by simpa only [Kr,norm_neg] using hb n (t-s)
  have hkr (n : ℕ) (s : ℝ) : star (Kr n s) = -Kr n s := by simp only [Kr,star_neg,hk]
  have hgr (n : ℕ) (s : ℝ) : S*Kr n s-Kr n s*S=Gr n s*S := by
    dsimp [Kr,Gr]
    calc
      _ = -(S*K n (t-s)-K n (t-s)*S) := by noncomm_ring
      _ = _ := by rw [hg,neg_mul]
  have hGr (n : ℕ) (s : ℝ) : ‖Gr n s‖ ≤ D := by simpa only [Gr,norm_neg] using hG n (t-s)
  have hδr (n m : ℕ) (s : ℝ) : ‖(Kr n s-Kr m s)*S‖ ≤ e n+e m := by
    have heq : (Kr n s-Kr m s)*S = -((K n (t-s)-K m (t-s))*S) := by dsimp [Kr]; noncomm_ring
    rw [heq,norm_neg]
    exact hδ n m (t-s)
  obtain ⟨R,hR⟩ := exists_evolution_limit Kr hKr M hM hbr hkr S hS hSd Gr hgr hGr hD e he he0 hδr t
  have hre (n : ℕ) : evolution (Kr n) t=star (evolution (K n) t) := by
    dsimp [Kr]
    rw [evolution_reverse (hK n) (hM n) (hb n) (hk n),sub_self,evolution_zero,one_mul]
  have hr : ∀ x, Tendsto (fun n => star (evolution (K n) t) x) atTop (𝓝 (R x)) := by
    simpa only [hre] using hR
  obtain ⟨hu,hs⟩ := unitary_of_strong_and_star_limit (fun n => evolution (K n) t)
    (fun n => evolution_mem_unitary (hK n) (hM n) (hb n) (hk n) t) L R hL hr
  refine ⟨L,hu,hL,?_⟩
  rwa [hs]

omit [Nontrivial H] in
 

lemma regularizer_factor_of_limits (F : ℕ → H →L[ℂ] H) (L : H →L[ℂ] H)
    (hl : ∀ x, Tendsto (fun n => star (F n) x) atTop (𝓝 (star L x)))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, ‖S (star (F n) x)‖ ≤ C*‖S x‖) :
    ∃ B : H →L[ℂ] H, L.comp S=S.comp B ∧ ‖B‖ ≤ C := by
  let Q := (S.comp (star L)).toLinearMap
  have hq (x : H) : ‖Q x‖ ≤ C*‖S.toLinearMap x‖ := by
    apply le_of_tendsto ((S.continuous.tendsto _).comp (hl x)).norm
    exact Filter.Eventually.of_forall (fun n => hb n x)
  let B := Q.extendOfNorm S.toLinearMap
  have he : B.comp S = S.comp (star L) := by
    ext x
    exact Q.extendOfNorm_eq hSd ⟨C,hq⟩ x
  have he' := congrArg ContinuousLinearMap.adjoint he
  have heq : S.comp B.adjoint=L.comp S := by
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using he'
  refine ⟨B.adjoint,heq.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact Q.opNorm_extendOfNorm_le hSd hC hq
end StronglyRationalVOA.TimeOrdered

open Set Filter
open scoped Topology
namespace StronglyRationalVOA.HilbertScale
variable {G : ℕ → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

def energyCutoff (n : ℕ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => if i ≤ n then 1 else 0) zero_le_one (by intro i; split_ifs <;> simp)

lemma energyCutoff_apply (n : ℕ) (x : Space G) (i : ℕ) :
    energyCutoff n x i = if i ≤ n then x i else 0 := by
  simp only [energyCutoff,boundedMultiplier_apply]
  split_ifs <;> simp
end StronglyRationalVOA.HilbertScale

end

end OAI
