import OAI.Topology.EilenbergGanea.UnitaryWords
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv

namespace OAI

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
/- Avoidance of an arbitrary open boundary makes the selected fiber
compact whenever the closure of the open set is compact. -/
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem compact_selected_fiber (f : E → E) (y : E) (U : Set E)
    (hU : IsOpen U) (hc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) : IsCompact (U ∩ f ⁻¹' {y}) := by
  have he : U ∩ f ⁻¹' {y} = closure U ∩ f ⁻¹' {y} := by
    ext x
    constructor
    · exact fun ⟨hx, hy⟩ => ⟨subset_closure hx, hy⟩
    · rintro ⟨hx, hy⟩
      refine ⟨?_, hy⟩
      by_contra hn
      exact hb x ⟨hx, by simpa only [hU.interior_eq] using hn⟩ hy
  rw [he]
  exact hc.of_isClosed_subset (hf.preimage_isClosed_of_isClosed isClosed_closure
    isClosed_singleton) inter_subset_left

/- The determinant retains its sign on a sufficiently small neighborhood
of a regular point. -/
theorem exists_constant_jacobian_sign_patch (f : E → E) {x : E}
    (hf : ContDiff ℝ 1 f) (hd : (fderiv ℝ f x).det ≠ 0) (W : Set E)
    (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ InjOn f V ∧ IsOpen (f '' V) ∧
      ∀ z ∈ V, (fderiv ℝ f z).det =
        (if 0 < (fderiv ℝ f x).det then 1 else -1) * |(fderiv ℝ f z).det| := by
  let d : E → ℝ := fun z => (fderiv ℝ f z).det
  have hc : Continuous d := ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hd
  have hf' : HasFDerivAt f (e : E →L[ℝ] E) x :=
    (hf.differentiable (by norm_num) x).hasFDerivAt
  let p := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by norm_num)
  have hxP : x ∈ p.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by norm_num)
  let A : Set E := if 0 < d x then {z | 0 < d z} else {z | d z < 0}
  have hA : IsOpen A := by
    dsimp [A]
    split_ifs
    · exact isOpen_lt continuous_const hc
    · exact isOpen_lt hc continuous_const
  have hxA : x ∈ A := by
    dsimp [A]
    split_ifs with hp
    · exact hp
    · exact lt_of_le_of_ne (le_of_not_gt hp) hd
  let V := W ∩ p.source ∩ A
  have hV : IsOpen V := (hW.inter p.open_source).inter hA
  refine ⟨V, hV, ⟨⟨hxW, hxP⟩, hxA⟩, fun _ h => h.1.1,
    p.injOn.mono (fun _ h => h.1.2), ?_, ?_⟩
  · exact p.isOpen_image_of_subset_source hV (fun _ h => h.1.2)
  · intro z hz
    have hzA := hz.2
    dsimp [A] at hzA
    split_ifs at hzA ⊢ with hp
    · change 0 < (fderiv ℝ f z).det at hzA
      simp [abs_of_pos hzA]
    · change (fderiv ℝ f z).det < 0 at hzA
      simp [abs_of_neg hzA]

/- Finitely many regular roots admit pairwise disjoint inverse neighborhoods,
all contained in the prescribed isolating open set. -/
theorem disjoint_regular_inverse_patches (f : E → E) (hf : ContDiff ℝ 1 f)
    (U : Set E) (hU : IsOpen U) (S : Set E) (hS : S.Finite)
    (hSU : S ⊆ U) (hd : ∀ x ∈ S, (fderiv ℝ f x).det ≠ 0) :
    ∃ V : S → Set E,
      (∀ x, IsOpen (V x) ∧ (x : E) ∈ V x ∧ V x ⊆ U ∧ InjOn f (V x) ∧
        IsOpen (f '' V x) ∧ ∀ z ∈ V x, (fderiv ℝ f z).det =
          (if 0 < (fderiv ℝ f x).det then 1 else -1) * |(fderiv ℝ f z).det|) ∧
      Pairwise (fun x y => Disjoint (V x) (V y)) := by
  classical
  obtain ⟨W, hW, hdisj⟩ := hS.t2_separation
  have hp (x : S) := exists_constant_jacobian_sign_patch f hf (hd x x.property)
    (U ∩ W x) (hU.inter (hW x).2) ⟨hSU x.property, (hW x).1⟩
  choose V hopen hmem hsub hinj himg hsign using hp
  refine ⟨V, fun x => ⟨hopen x, hmem x, fun _ h => (hsub x h).1,
    hinj x, himg x, hsign x⟩, ?_⟩
  intro x y hxy
  exact (hdisj x.property y.property (fun he => hxy (Subtype.ext he))).mono
    (fun _ h => (hsub x h).2) (fun _ h => (hsub y h).2)

/- Compactness shrinks the target neighborhood so that all selected
preimages remain in the chosen inverse patches. It does not assert a
smooth boundary or a proper global map. -/
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_target_neighborhood_of_patches {ι : Type*} [Fintype ι]
    (f : E → E) (y : E) (U : Set E) (hU : IsOpen U)
    (hc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) (V : ι → Set E)
    (hV : ∀ i, IsOpen (V i)) (himg : ∀ i, IsOpen (f '' V i))
    (hy : ∀ i, y ∈ f '' V i)
    (hcover : ∀ x ∈ U, f x = y → ∃ i, x ∈ V i) :
    ∃ N : Set E, IsOpen N ∧ y ∈ N ∧ (∀ i, N ⊆ f '' V i) ∧
      ∀ x ∈ U, f x ∈ N → ∃ i, x ∈ V i := by
  let K := closure U \ ⋃ i, V i
  have hK : IsCompact K := hc.diff (isOpen_iUnion hV)
  have hclosed : IsClosed (f '' K) := (hK.image_of_continuousOn
    (hf.mono (fun _ h => h.1))).isClosed
  have hyK : y ∉ f '' K := by
    rintro ⟨x, ⟨hxcl, hxV⟩, hxy⟩
    have hxU : x ∈ U := by
      by_contra hn
      exact hb x ⟨hxcl, by simpa only [hU.interior_eq] using hn⟩ hxy
    obtain ⟨i, hi⟩ := hcover x hxU hxy
    exact hxV (mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨(f '' K)ᶜ ∩ ⋂ i, f '' V i,
    hclosed.isOpen_compl.inter (isOpen_iInter_of_finite himg),
    ⟨hyK, mem_iInter.mpr hy⟩, ?_, ?_⟩
  · intro i z hz
    exact mem_iInter.mp hz.2 i
  · intro x hxU hxN
    by_contra hn
    apply hxN.1
    refine ⟨x, ⟨subset_closure hxU, ?_⟩, rfl⟩
    simpa only [mem_iUnion] using hn

end EilenbergGanea

open Set MeasureTheory
namespace EilenbergGanea
section SignedIntegralDegree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/- The integral representative of local degree against a target bump. -/
def jacobianIntegral (f : E → E) (U : Set E) (ρ : E → ℝ) : ℝ :=
  ∫ x in U, (fderiv ℝ f x).det * ρ (f x) ∂μ

/- The signed change-of-variables formula on one regular inverse patch. -/
theorem jacobianIntegral_of_injOn (f : E → E) (U : Set E) (hU : MeasurableSet U)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : InjOn f U)
    (ρ : E → ℝ) (σ : ℝ) (hσ : ∀ x ∈ U,
      (fderiv ℝ f x).det = σ * |(fderiv ℝ f x).det|) :
    jacobianIntegral μ f U ρ = σ * ∫ y in f '' U, ρ y ∂μ := by
  have hc := integral_image_eq_integral_abs_det_fderiv_smul μ hU
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj ρ
  rw [jacobianIntegral, hc, ← integral_const_mul]
  apply setIntegral_congr_fun hU
  intro x hx
  dsimp only
  calc
    _ = (σ * |(fderiv ℝ f x).det|) * ρ (f x) := congrArg (· * ρ (f x)) (hσ x hx)
    _ = _ := by simp only [smul_eq_mul, mul_assoc]

/- If the normalized target bump is supported inside an inverse patch, the
patch contributes exactly the sign of its Jacobian. -/
theorem jacobianIntegral_inverse_patch (f : E → E) (U : Set E) (hU : MeasurableSet U)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : InjOn f U)
    (ρ : E → ℝ) (σ : ℝ) (hσ : ∀ x ∈ U,
      (fderiv ℝ f x).det = σ * |(fderiv ℝ f x).det|)
    (hsupp : Function.support ρ ⊆ f '' U) (hunit : ∫ y, ρ y ∂μ = 1) :
    jacobianIntegral μ f U ρ = σ := by
  rw [jacobianIntegral_of_injOn μ f U hU hf hinj ρ σ hσ]
  have he : (∫ y in f '' U, ρ y ∂μ) = ∫ y, ρ y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_contra hn
    exact hy (hsupp hn)
  rw [he, hunit, mul_one]

/- Excision and finite additivity of the analytic degree representative. -/
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem jacobianIntegral_sum_patches {ι : Type*} [Fintype ι]
    (f : E → E) (U : Set E) (hU : MeasurableSet U) (V : ι → Set E)
    (hV : ∀ i, MeasurableSet (V i)) (hsub : ∀ i, V i ⊆ U)
    (hdisj : Pairwise (fun i j => Disjoint (V i) (V j))) (ρ : E → ℝ)
    (hsupp : ∀ x ∈ U, ρ (f x) ≠ 0 → ∃ i, x ∈ V i)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ) :
    jacobianIntegral μ f U ρ = ∑ i, jacobianIntegral μ f (V i) ρ := by
  unfold jacobianIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU
    (iUnion_subset hsub)]
  · exact integral_iUnion_fintype hV hdisj (fun i => hint.mono_set (hsub i))
  · rintro x ⟨hxU, hxV⟩
    have hz : ρ (f x) = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := hsupp x hxU hn
      exact hxV (mem_iUnion.mpr ⟨i, hi⟩)
    rw [hz, mul_zero]

/- The regular signed-count formula, once disjoint inverse patches and a
small normalized target bump have been chosen. -/
theorem jacobianIntegral_eq_sum_signs {ι : Type*} [Fintype ι]
    (f : E → E) (U : Set E) (hU : MeasurableSet U) (V : ι → Set E)
    (hV : ∀ i, MeasurableSet (V i)) (hsub : ∀ i, V i ⊆ U)
    (hdisj : Pairwise (fun i j => Disjoint (V i) (V j)))
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : ∀ i, InjOn f (V i))
    (ρ : E → ℝ) (σ : ι → ℝ)
    (hσ : ∀ i x, x ∈ V i → (fderiv ℝ f x).det = σ i * |(fderiv ℝ f x).det|)
    (hcovered : ∀ x ∈ U, ρ (f x) ≠ 0 → ∃ i, x ∈ V i)
    (hsupp : ∀ i, Function.support ρ ⊆ f '' V i)
    (hunit : ∫ y, ρ y ∂μ = 1)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ) :
    jacobianIntegral μ f U ρ = ∑ i, σ i := by
  rw [jacobianIntegral_sum_patches μ f U hU V hV hsub hdisj ρ hcovered hint]
  apply Finset.sum_congr rfl
  intro i _
  exact jacobianIntegral_inverse_patch μ f (V i) (hV i)
    (fun x hx => hf x (hsub i hx)) (hinj i) ρ (σ i) (hσ i) (hsupp i) hunit

/- A vanishing selected preimage forces every supported degree integral to
vanish. This implication supplies existence from nonzero degree. -/
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem jacobianIntegral_eq_zero_of_no_preimage (f : E → E) (U : Set E) (ρ : E → ℝ)
    (h : ∀ x ∈ U, ρ (f x) = 0) : jacobianIntegral μ f U ρ = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  simp only [h x hx, mul_zero]

end SignedIntegralDegree
end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A normalized smooth target bump can be supported in any prescribed
neighborhood of the target. -/
theorem exists_normalized_smooth_bump (y : E) (N : Set E) (hN : IsOpen N) (hy : y ∈ N) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ N ∧
      (∫ z, ρ z ∂μ) = 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN y hy
  let b : ContDiffBump y := ⟨r / 4, r / 2, by linarith, by linarith⟩
  refine ⟨b.normed μ, b.contDiff_normed, b.hasCompactSupport_normed,
    ?_, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro z hz
  apply hball
  exact lt_of_le_of_lt hz (by change r / 2 < r; linarith)

/-- One target neighborhood works for every normalized continuous density.
This uniformity lets the same density be used throughout a localized homotopy. -/
theorem regular_signed_count_neighborhood (f : E → E) (hf : ContDiff ℝ 1 f)
    (y : E) (U : Set E) (hU : IsOpen U) (hc : IsCompact (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) (s : Finset E)
    (hs : ∀ x, x ∈ s ↔ x ∈ U ∧ f x = y)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) :
    ∃ N : Set E, IsOpen N ∧ y ∈ N ∧ ∀ ρ : E → ℝ, Continuous ρ →
      Function.support ρ ⊆ N → (∫ z, ρ z ∂μ) = 1 →
      jacobianIntegral μ f U ρ = ∑ x ∈ s, (if 0 < (fderiv ℝ f x).det then 1 else -1) := by
  classical
  obtain ⟨V, hV, hdisj⟩ := disjoint_regular_inverse_patches f hf U hU
    (s : Set E) s.finite_toSet (fun x hx => ((hs x).mp hx).1) hd
  obtain ⟨N, hN, hyN, hNimg, hNpre⟩ := exists_target_neighborhood_of_patches f y U hU
    hc hf.continuous.continuousOn hb V (fun i => (hV i).1)
    (fun i => (hV i).2.2.2.2.1)
    (fun i => ⟨i, (hV i).2.1, ((hs i).mp i.property).2⟩)
    (fun x hx hxy => ⟨⟨x, (hs x).mpr ⟨hx, hxy⟩⟩, (hV _).2.1⟩)
  refine ⟨N, hN, hyN, fun ρ hρ hρN hρunit => ?_⟩
  have hcont : Continuous (fun x => (fderiv ℝ f x).det * ρ (f x)) :=
    (ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by norm_num))).mul
      (hρ.comp hf.continuous)
  have hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ :=
    (hcont.continuousOn.integrableOn_compact hc).mono_set subset_closure
  have hcount := jacobianIntegral_eq_sum_signs μ f U hU.measurableSet V
    (fun i => (hV i).1.measurableSet) (fun i => (hV i).2.2.1) hdisj
    (fun x _ => hf.differentiable (by norm_num) x) (fun i => (hV i).2.2.2.1)
    ρ (fun i => if 0 < (fderiv ℝ f i).det then 1 else -1)
    (fun i => (hV i).2.2.2.2.2)
    (fun x hx hn => hNpre x hx (hρN hn))
    (fun i z hz => hNimg i (hρN hz)) hρunit hint
  exact hcount.trans (Finset.sum_subtype (p := fun x => x ∈ (s : Set E)) s
    (fun _ => Iff.rfl) (fun x => (if 0 < (fderiv ℝ f x).det then 1 else -1 : ℝ))).symm

/-- The analytic representative has exactly the expected signed regular
count for a sufficiently concentrated normalized target bump. -/
theorem regular_signed_count_density (f : E → E) (hf : ContDiff ℝ 1 f)
    (y : E) (U : Set E) (hU : IsOpen U) (hc : IsCompact (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) (s : Finset E)
    (hs : ∀ x, x ∈ s ↔ x ∈ U ∧ f x = y)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ (∫ z, ρ z ∂μ) = 1 ∧
      jacobianIntegral μ f U ρ = ∑ x ∈ s, (if 0 < (fderiv ℝ f x).det then 1 else -1) := by
  classical
  obtain ⟨V, hV, hdisj⟩ := disjoint_regular_inverse_patches f hf U hU
    (s : Set E) s.finite_toSet (fun x hx => ((hs x).mp hx).1) hd
  obtain ⟨N, hN, hyN, hNimg, hNpre⟩ := exists_target_neighborhood_of_patches f y U hU
    hc hf.continuous.continuousOn hb V (fun i => (hV i).1)
    (fun i => (hV i).2.2.2.2.1)
    (fun i => ⟨i, (hV i).2.1, ((hs i).mp i.property).2⟩)
    (fun x hx hxy => ⟨⟨x, (hs x).mpr ⟨hx, hxy⟩⟩, (hV _).2.1⟩)
  obtain ⟨ρ, hρ, hρc, hρN, hρunit⟩ := exists_normalized_smooth_bump μ y N hN hyN
  refine ⟨ρ, hρ, hρc, hρunit, ?_⟩
  have hcont : Continuous (fun x => (fderiv ℝ f x).det * ρ (f x)) :=
    (ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by norm_num))).mul
      (hρ.continuous.comp hf.continuous)
  have hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ :=
    (hcont.continuousOn.integrableOn_compact hc).mono_set subset_closure
  have hcount := jacobianIntegral_eq_sum_signs μ f U hU.measurableSet V
    (fun i => (hV i).1.measurableSet) (fun i => (hV i).2.2.1) hdisj
    (fun x _ => hf.differentiable (by norm_num) x) (fun i => (hV i).2.2.2.1)
    ρ (fun i => if 0 < (fderiv ℝ f i).det then 1 else -1)
    (fun i => (hV i).2.2.2.2.2)
    (fun x hx hn => hNpre x hx (hρN (subset_tsupport ρ hn)))
    (fun i z hz => hNimg i (hρN (subset_tsupport ρ hz))) hρunit hint
  exact hcount.trans (Finset.sum_subtype (p := fun x => x ∈ (s : Set E)) s
    (fun _ => Iff.rfl) (fun x => (if 0 < (fderiv ℝ f x).det then 1 else -1 : ℝ))).symm

end EilenbergGanea

open Set MeasureTheory Filter Topology
namespace EilenbergGanea

/-- Standard coordinate basis as a tuple of vectors. -/
def coordinateBasis (n : ℕ) : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1

/-- The signed coordinate coefficient of an n-form in dimension n+1. -/
def formFlux {n : ℕ} (form : (Fin (n + 1) → ℝ) →
    (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (-1 : ℝ) ^ i.val * form x (i.removeNth (coordinateBasis (n + 1)))

/-- Stokes on a rectangular box, as a direct consequence of Mathlib's
Bochner divergence theorem. No smoothness of an arbitrary open-set boundary
is assumed in the later application. -/
theorem integral_extDeriv_box {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (hint : IntegrableOn (fun x => extDeriv form x (coordinateBasis (n + 1))) (Icc a b)) :
    (∫ x in Icc a b, extDeriv form x (coordinateBasis (n + 1))) =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (a i) x)) := by
  have hd (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
      DifferentiableAt ℝ (formFlux form i) x := by
    exact ((hform x).continuousAlternatingMap_apply_const _).const_mul _
  have he (x : Fin (n + 1) → ℝ) :
      (∑ i : Fin (n + 1), fderiv ℝ (formFlux form i) x (Pi.single i 1)) =
        extDeriv form x (coordinateBasis (n + 1)) := by
    rw [extDeriv_apply (hform x)]
    apply Finset.sum_congr rfl
    intro i _
    change (fderiv ℝ (fun y => (-1 : ℝ) ^ i.val *
      form y (i.removeNth (coordinateBasis (n + 1)))) x) (Pi.single i 1) = _
    rw [fderiv_const_mul ((hform x).continuousAlternatingMap_apply_const _) ]
    simp [coordinateBasis]
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (formFlux form) (fun i x => fderiv ℝ (formFlux form i) x) ∅ countable_empty
    (fun i => (show Differentiable ℝ (formFlux form i) from hd i).continuous.continuousOn)
    (fun x _ i => (hd i x).hasFDerivAt) (by simpa only [he] using hint)
  simpa only [he] using h

/-- Every top-degree differential form on Euclidean n-space is closed. -/
theorem extDeriv_topForm_eq_zero {n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (x : Fin n → ℝ) :
    extDeriv φ x = 0 := by
  ext v
  apply (extDeriv φ x).toAlternatingMap.map_linearDependent
  intro hv
  have h := hv.fintype_card_le_finrank
  simp at h

/-- The pullback of a top form by a C² map is closed (the Piola identity). -/
theorem extDeriv_pullback_topForm_eq_zero {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : Differentiable ℝ φ) (F : E → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F) (x : E) :
    extDeriv (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y)) x = 0 := by
  rw [extDeriv_pullback (hφ _) hF.contDiffAt (by simp), extDeriv_topForm_eq_zero]
  ext v
  rfl


/-- A closed form has total signed flux zero across the faces of a box. -/
theorem closedForm_boundary_box {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (hclosed : ∀ x, extDeriv form x = 0)
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) :
    (∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (a i) x))) = 0 := by
  have hz (x) : extDeriv form x (coordinateBasis (n + 1)) = 0 := by rw [hclosed]; rfl
  have h := integral_extDeriv_box form hform a b hab (by simpa only [hz] using integrableOn_zero)
  simpa only [hz, integral_zero] using h.symm

/-- The coefficient integrals on two opposing faces of a box agree for a
closed form whose flux on all other faces is zero. This is the analytic
homotopy-invariance step with the sides outside the support of the form. -/
theorem closedForm_opposite_faces {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (hclosed : ∀ x, extDeriv form x = 0)
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) (k : Fin (n + 1))
    (hside : ∀ i, i ≠ k → ∀ x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      formFlux form i (i.insertNth (b i) x) = 0 ∧
      formFlux form i (i.insertNth (a i) x) = 0) :
    (∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux form k (k.insertNth (b k) x)) =
    ∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux form k (k.insertNth (a k) x) := by
  have h := closedForm_boundary_box form hform hclosed a b hab
  rw [Finset.sum_eq_single k] at h
  · exact sub_eq_zero.mp h
  · intro i _ hi
    have hb0 : (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux form i (i.insertNth (b i) x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hside i hi x hx).1
    have ha0 : (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux form i (i.insertNth (a i) x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hside i hi x hx).2
    rw [hb0, ha0, sub_self]
  · simp

/-- Determinant form with the standard coordinate orientation. -/
def coordinateVolumeForm (n : ℕ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

/-- Smooth pullbacks of a top form are differentiable. -/
theorem differentiable_pullback_topForm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : Differentiable ℝ φ) (F : E → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y)) := by
  intro x
  apply ((hφ (F x)).comp x (hF.differentiable (by norm_num) x)
    ).continuousAlternatingMapCompContinuousLinearMap
  exact (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x


/-- Restricting a field to an open set whose boundary avoids its topological
support is locally either the original field or zero. -/
theorem indicator_eventuallyEq_or_zero {X A : Type*} [TopologicalSpace X] [Zero A]
    (U : Set X) (hU : IsOpen U) (f : X → A)
    (hb : Disjoint (frontier U) (tsupport f)) (x : X) :
    U.indicator f =ᶠ[nhds x] f ∨ U.indicator f =ᶠ[nhds x] fun _ => 0 := by
  classical
  by_cases hx : x ∈ U
  · left
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy f
  · right
    by_cases hc : x ∈ closure U
    · have hf : x ∉ tsupport f := by
        apply Set.disjoint_left.mp hb
        exact ⟨hc, by simpa only [hU.interior_eq] using hx⟩
      have he := notMem_tsupport_iff_eventuallyEq.mp hf
      filter_upwards [he] with y hy
      by_cases hyU : y ∈ U <;> simp [Set.indicator, hyU, hy]
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
      exact Set.indicator_of_notMem (fun hyU => hy (subset_closure hyU)) f

/-- Excision at the differential-form level: cutting off at an arbitrary
isolating open-set boundary preserves differentiability and closedness. -/
theorem localized_closedForm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (form : E → E [⋀^Fin n]→L[ℝ] ℝ) (hform : Differentiable ℝ form)
    (hclosed : ∀ x, extDeriv form x = 0) (U : Set E) (hU : IsOpen U)
    (hb : Disjoint (frontier U) (tsupport form)) :
    Differentiable ℝ (U.indicator form) ∧ ∀ x, extDeriv (U.indicator form) x = 0 := by
  constructor
  · intro x
    rcases indicator_eventuallyEq_or_zero U hU form hb x with hx | hx
    · exact (hform x).congr_of_eventuallyEq hx
    · exact differentiableAt_const (c := (0 : E [⋀^Fin n]→L[ℝ] ℝ)) |>.congr_of_eventuallyEq hx
  · intro x
    rcases indicator_eventuallyEq_or_zero U hU form hb x with hx | hx
    · rw [hx.extDeriv_eq, hclosed]
    · rw [hx.extDeriv_eq]
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- Homotopy-invariant integrals of a pulled-back target top form, with no
unproved mapping-degree primitive. -/
theorem pullback_topForm_opposite_faces {n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : Differentiable ℝ φ) (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ))
    (hF : ContDiff ℝ 2 F) (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (k : Fin (n + 1))
    (hside : ∀ i, i ≠ k → ∀ x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      φ (F (i.insertNth (b i) x)) = 0 ∧ φ (F (i.insertNth (a i) x)) = 0) :
    (∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y))
        k (k.insertNth (b k) x)) =
    ∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y))
        k (k.insertNth (a k) x) := by
  apply closedForm_opposite_faces _ (differentiable_pullback_topForm φ hφ F hF)
    (extDeriv_pullback_topForm_eq_zero φ hφ F hF) a b hab k
  intro i hi x hx
  obtain ⟨hb, ha⟩ := hside i hi x hx
  simp [formFlux, hb, ha]


/-- Evaluation of the standard volume form is the ordinary linear
 determinant. -/
theorem coordinateVolumeForm_linear {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordinateVolumeForm n (fun i => L (coordinateBasis n i)) = L.det := by
  change Matrix.det (fun i => L (Pi.single i 1)) = _
  calc
    _ = (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      L.toLinearMap).transpose.det := by
        congr 1
    _ = _ := by rw [Matrix.det_transpose, LinearMap.det_toMatrix]

/-- At a temporal face, the pullback coefficient is precisely the signed
Jacobian density of the corresponding slice. -/
theorem formFlux_pullback_first_face {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ))
    (t : ℝ) (x : Fin n → ℝ) (hF : DifferentiableAt ℝ F (Fin.cons t x)) :
    formFlux (fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
      (fderiv ℝ F y)) 0 (Fin.cons t x) =
      (fderiv ℝ (fun z => F (Fin.cons t z)) x).det * ρ (F (Fin.cons t x)) := by
  let J : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    (0 : (Fin n → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin n → ℝ))
  have hJ : HasFDerivAt (fun z : Fin n → ℝ => Fin.cons t z) J x :=
    (hasFDerivAt_const t x).finCons (hasFDerivAt_id x)
  have hs := hF.hasFDerivAt.comp x hJ
  have he (i : Fin n) : J (coordinateBasis n i) = coordinateBasis (n + 1) i.succ := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [J, coordinateBasis, ContinuousLinearMap.finCons]
    · simp [J, coordinateBasis, ContinuousLinearMap.finCons, Pi.single_apply]
  have hs' : fderiv ℝ (fun z => F (Fin.cons t z)) x =
      (fderiv ℝ F (Fin.cons t x)).comp J := hs.fderiv
  rw [hs']
  have hd := coordinateVolumeForm_linear ((fderiv ℝ F (Fin.cons t x)).comp J)
  simp only [ContinuousLinearMap.comp_apply, he] at hd
  simp only [formFlux, Fin.val_zero, pow_zero, one_mul, Fin.removeNth_zero,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1

/-- Smooth homotopy invariance of the Jacobian integral against a target
bump whose pullback vanishes on the spatial sides of a containing box. -/
theorem jacobian_integral_homotopy_box {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (a b : Fin n → ℝ) (hab : a ≤ b)
    (hside : ∀ i : Fin (n + 1), i ≠ 0 →
      ∀ x ∈ Icc ((Fin.cons t₀ a : Fin (n + 1) → ℝ) ∘ i.succAbove)
        ((Fin.cons t₁ b : Fin (n + 1) → ℝ) ∘ i.succAbove),
      ρ (F (i.insertNth ((Fin.cons t₁ b : Fin (n + 1) → ℝ) i) x)) = 0 ∧
      ρ (F (i.insertNth ((Fin.cons t₀ a : Fin (n + 1) → ℝ) i) x)) = 0) :
    (∫ x in Icc a b, (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det *
      ρ (F (Fin.cons t₁ x))) =
    ∫ x in Icc a b, (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det *
      ρ (F (Fin.cons t₀ x)) := by
  have hφ : Differentiable ℝ (fun y => ρ y • coordinateVolumeForm n) :=
    hρ.smul_const _
  have hbox : (Fin.cons t₀ a : Fin (n + 1) → ℝ) ≤ Fin.cons t₁ b := by
    intro i
    exact Fin.cases ht (fun j => hab j) i
  have h := pullback_topForm_opposite_faces (fun y => ρ y • coordinateVolumeForm n)
    hφ F hF (Fin.cons t₀ a) (Fin.cons t₁ b) hbox 0 (by
      intro i hi x hx
      obtain ⟨h₁, h₀⟩ := hside i hi x hx
      simp only [h₁, h₀, zero_smul, and_self])
  have hins (t : ℝ) (x : Fin n → ℝ) :
      (0 : Fin (n + 1)).insertNth t x = (Fin.cons t x : Fin (n + 1) → ℝ) := by
    simp only [Fin.insertNth_zero, cast_eq]
  simpa only [Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, Fin.cons_zero,
    hins, formFlux_pullback_first_face ρ F _ _ (hF.differentiable (by norm_num) _)] using h


/-- The support of a pulled-back density lies above the support of the target
bump. This provides the needed collar at an arbitrary isolating boundary. -/
theorem tsupport_pullback_density_subset {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : (Fin n → ℝ) → ℝ) (F : E → (Fin n → ℝ)) (hF : Continuous F) :
    tsupport (fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
      (fderiv ℝ F y)) ⊆ F ⁻¹' tsupport ρ := by
  apply closure_minimal _ ((isClosed_tsupport ρ).preimage hF)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by ext v; simp [hz])

/-- Localized homotopy invariance on an arbitrary open spatial set. The
boundary collar is expressed by avoidance of the target bump, not by a smooth
boundary assumption. The spatial box is only an integration device. -/
theorem jacobian_integral_homotopy_localized_box {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hboundary : ∀ y : Fin (n + 1) → ℝ,
      (fun i => y i.succ) ∈ frontier U → F y ∉ tsupport ρ)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (a b : Fin n → ℝ) (hab : a ≤ b)
    (hbox : U ⊆ Icc a b)
    (hside : ∀ i : Fin (n + 1), i ≠ 0 →
      ∀ x ∈ Icc ((Fin.cons t₀ a : Fin (n + 1) → ℝ) ∘ i.succAbove)
        ((Fin.cons t₁ b : Fin (n + 1) → ℝ) ∘ i.succAbove),
      (fun j : Fin n => (i.insertNth ((Fin.cons t₁ b : Fin (n + 1) → ℝ) i) x :
        Fin (n + 1) → ℝ) j.succ) ∉ U ∧
      (fun j : Fin n => (i.insertNth ((Fin.cons t₀ a : Fin (n + 1) → ℝ) i) x :
        Fin (n + 1) → ℝ) j.succ) ∉ U) :
    (∫ x in U, (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det *
      ρ (F (Fin.cons t₁ x))) =
    ∫ x in U, (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det *
      ρ (F (Fin.cons t₀ x)) := by
  classical
  let π : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun y i => y i.succ
  have hπ : Continuous π := continuous_pi (fun i => continuous_apply i.succ)
  let C := π ⁻¹' U
  let form := fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
    (fderiv ℝ F y)
  have hc : Disjoint (frontier C) (tsupport form) := by
    apply disjoint_left.mpr
    intro y hy hs
    exact hboundary y ((hπ.frontier_preimage_subset U) hy)
      (tsupport_pullback_density_subset ρ F hF.continuous hs)
  obtain ⟨hd, hz⟩ := localized_closedForm form
    (differentiable_pullback_topForm _ (hρ.smul_const _) F hF)
    (extDeriv_pullback_topForm_eq_zero _ (hρ.smul_const _) F hF) C
    (hU.preimage hπ) hc
  have htbox : (Fin.cons t₀ a : Fin (n + 1) → ℝ) ≤ Fin.cons t₁ b := by
    intro i
    exact Fin.cases ht (fun j => hab j) i
  have he := closedForm_opposite_faces (C.indicator form) hd hz
    (Fin.cons t₀ a) (Fin.cons t₁ b) htbox 0 (by
      intro i hi x hx
      obtain ⟨h₁, h₀⟩ := hside i hi x hx
      have hc₁ : i.insertNth ((Fin.cons t₁ b : Fin (n + 1) → ℝ) i) x ∉ C := h₁
      have hc₀ : i.insertNth ((Fin.cons t₀ a : Fin (n + 1) → ℝ) i) x ∉ C := h₀
      simp [formFlux, indicator_of_notMem hc₁, indicator_of_notMem hc₀])
  have hface (t : ℝ) (x : Fin n → ℝ) :
      formFlux (C.indicator form) 0 (Fin.cons t x) =
        U.indicator (fun z => (fderiv ℝ (fun w => F (Fin.cons t w)) z).det *
          ρ (F (Fin.cons t z))) x := by
    by_cases hx : x ∈ U
    · have hc : Fin.cons t x ∈ C := by simpa only [C, mem_preimage, π, Fin.cons_succ] using hx
      rw [indicator_of_mem hx]
      change (-1 : ℝ) ^ (0 : Fin (n + 1)).val *
        (C.indicator form) (Fin.cons t x) _ = _
      rw [indicator_of_mem hc]
      exact formFlux_pullback_first_face ρ F t x (hF.differentiable (by norm_num) _)
    · have hc : Fin.cons t x ∉ C := by simpa only [C, mem_preimage, π, Fin.cons_succ] using hx
      simp [formFlux, hc, hx]
  have hins (t : ℝ) (x : Fin n → ℝ) :
      (0 : Fin (n + 1)).insertNth t x = (Fin.cons t x : Fin (n + 1) → ℝ) := by
    simp only [Fin.insertNth_zero, cast_eq]
  simpa only [Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, Fin.cons_zero,
    hins, hface, setIntegral_indicator hU.measurableSet,
    inter_eq_right.mpr hbox] using he


/-- Homotopy invariance on a bounded open set, without selecting a box or
requiring any shape or smoothness of its boundary. -/
theorem jacobian_integral_homotopy_localized {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hboundary : ∀ y : Fin (n + 1) → ℝ,
      (fun i => y i.succ) ∈ frontier U → F y ∉ tsupport ρ)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    (∫ x in U, (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det *
      ρ (F (Fin.cons t₁ x))) =
    ∫ x in U, (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det *
      ρ (F (Fin.cons t₀ x)) := by
  obtain ⟨R, hR, hbound⟩ := hUb.exists_pos_norm_lt
  have hcoord (x) (hx : x ∈ U) (i : Fin n) : |x i| < R :=
    lt_of_le_of_lt (norm_le_pi_norm x i) (hbound x hx)
  have hout (x : Fin n → ℝ) (i : Fin n) (hx : x i = R ∨ x i = -R) : x ∉ U := by
    intro hxu
    have h := hcoord x hxu i
    rcases hx with hx | hx <;> rw [hx] at h
    · simp only [abs_of_pos hR, lt_self_iff_false] at h
    · simp only [abs_neg, abs_of_pos hR, lt_self_iff_false] at h
  apply jacobian_integral_homotopy_localized_box ρ hρ F hF U hU hboundary
    t₀ t₁ ht (fun _ => -R) (fun _ => R) (fun _ => by linarith)
  · intro x hx
    constructor <;> intro i
    · exact (abs_lt.mp (hcoord x hx i)).1.le
    · exact (abs_lt.mp (hcoord x hx i)).2.le
  · intro i hi x _
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    constructor
    · apply hout _ j
      left
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]
    · apply hout _ j
      right
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]


/-- Only boundary avoidance during the given interval is needed. Smooth
saturation of the time coordinate turns it into the global collar hypothesis
of the preceding Stokes argument, with the endpoints unchanged. -/
theorem jacobian_integral_homotopy_localized_interval {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U,
      F (Fin.cons t x) ∉ tsupport ρ) :
    (∫ x in U, (fderiv ℝ (fun z => F (Fin.cons 1 z)) x).det *
      ρ (F (Fin.cons 1 x))) =
    ∫ x in U, (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det *
      ρ (F (Fin.cons 0 x)) := by
  let H : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun y =>
    F (Fin.cons (Real.smoothTransition (y 0)) (Fin.tail y))
  have hH : ContDiff ℝ 2 H := by
    apply hF.comp
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 0)
    · exact contDiff_apply ℝ ℝ j.succ
  have hb : ∀ y : Fin (n + 1) → ℝ,
      (fun i => y i.succ) ∈ frontier U → H y ∉ tsupport ρ := by
    intro y hy
    exact hboundary _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ _ hy
  have h := jacobian_integral_homotopy_localized ρ hρ H hH U hU hUb hb 0 1 zero_le_one
  simpa only [H, Fin.cons_zero, Fin.tail_cons, Real.smoothTransition.zero,
    Real.smoothTransition.one] using h

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory

/-- A nonzero signed regular count cannot disappear under a smooth homotopy
whose boundary avoids the target. All analytic degree ingredients are proved
above; in particular this is not an assumed Brouwer-degree interface. -/
theorem regular_count_persists {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (y : Fin n → ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hc : IsCompact (closure U))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, F (Fin.cons t x) ≠ y)
    (s : Finset (Fin n → ℝ))
    (hs : ∀ x, x ∈ s ↔ x ∈ U ∧ F (Fin.cons 0 x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) :
    ∃ x ∈ U, F (Fin.cons 1 x) = y := by
  classical
  by_contra hno
  have hno' : ∀ x ∈ U, F (Fin.cons 1 x) ≠ y := by simpa only [not_exists, not_and] using hno
  let f₀ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => F (Fin.cons 0 x)
  let f₁ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => F (Fin.cons 1 x)
  have hcons (t : ℝ) : ContDiff ℝ 2 (fun x : Fin n → ℝ =>
      (Fin.cons t x : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases contDiff_const (fun j => ?_) i
    exact contDiff_apply ℝ ℝ j
  have hf₀ : ContDiff ℝ 1 f₀ := (hF.comp (hcons 0)).of_le (by norm_num)
  have hf₁ : Continuous f₁ := (hF.comp (hcons 1)).continuous
  obtain ⟨N, hN, hyN, hsign⟩ := regular_signed_count_neighborhood volume f₀ hf₀
    y U hU hc (hb 0 (by simp)) s hs hd
  let K : Set (Fin n → ℝ) :=
    (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) '' (Icc (0 : ℝ) 1 ×ˢ frontier U)
  have hfront : IsCompact (frontier U) := hc.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hK : IsCompact K := (isCompact_Icc.prod hfront).image
    (hF.continuous.comp (by
      apply continuous_pi
      intro i
      exact Fin.cases continuous_fst
        (fun j => (continuous_apply j).comp continuous_snd) i))
  have hyK : y ∉ K := by
    rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, he⟩
    exact hb t ht x hx he
  have hy₁ : y ∉ f₁ '' closure U := by
    rintro ⟨x, hx, he⟩
    by_cases hxU : x ∈ U
    · exact hno' x hxU he
    · exact hb 1 (by simp) x ⟨hx, by simpa only [hU.interior_eq] using hxU⟩ he
  let M := N \ (K ∪ f₁ '' closure U)
  have hM : IsOpen M := hN.sdiff (hK.isClosed.union (hc.image hf₁).isClosed)
  have hyM : y ∈ M := ⟨hyN, fun h => h.elim hyK hy₁⟩
  obtain ⟨ρ, hρ, _, hρM, hunit⟩ := exists_normalized_smooth_bump volume y M hM hyM
  have hρN : Function.support ρ ⊆ N := fun z hz => (hρM (subset_tsupport ρ hz)).1
  have hval : jacobianIntegral volume f₀ U ρ =
      ∑ x ∈ s, (if 0 < (fderiv ℝ f₀ x).det then 1 else -1) :=
    hsign ρ hρ.continuous hρN hunit
  have hcollar : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U,
      F (Fin.cons t x) ∉ tsupport ρ := by
    intro t ht x hx hsup
    exact (hρM hsup).2 (Or.inl ⟨(t, x), ⟨ht, hx⟩, rfl⟩)
  have hinv := jacobian_integral_homotopy_localized_interval ρ
    (hρ.differentiable (by simp)) F hF U hU
    (hc.isBounded.subset subset_closure) hcollar
  have hzero : jacobianIntegral volume f₁ U ρ = 0 := by
    apply jacobianIntegral_eq_zero_of_no_preimage
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hsup
    exact (hρM hsup).2 (Or.inr ⟨x, subset_closure hx, rfl⟩)
  apply hcount
  exact hval.symm.trans (hinv.symm.trans hzero)

end EilenbergGanea

namespace EilenbergGanea
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The analytic nonzero-count theorem is independent of a choice of linear
coordinates. This form applies directly to finite products of quaternions. -/
theorem regular_count_persists_finiteDimensional
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F)
    (y : E) (U : Set E) (hU : IsOpen U) (hc : IsCompact (closure U))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, F (t, x) ≠ y)
    (s : Finset E) (hs : ∀ x, x ∈ s ↔ x ∈ U ∧ F (0, x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (0, z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (0, z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) : ∃ x ∈ U, F (1, x) = y := by
  classical
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ E).equivFunL
  let G : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
    fun z => e (F (z 0, e.symm (Fin.tail z)))
  have hG : ContDiff ℝ 2 G := by
    apply e.contDiff.comp
    apply hF.comp
    exact (contDiff_apply ℝ ℝ 0).prodMk (e.symm.contDiff.comp
      (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ i.succ)))
  have hdet (x : E) :
      (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det =
      (fderiv ℝ (fun z => F (0, z)) x).det := by
    have h₀ : DifferentiableAt ℝ (fun z => F (0, z)) x :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
    have h₀' : HasFDerivAt (fun z => F (0, z))
        (fderiv ℝ (fun z => F (0, z)) x) (e.symm (e x)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using h₀.hasFDerivAt
    have hcomp := e.hasFDerivAt.comp (e x)
      (h₀'.comp (e x) e.symm.hasFDerivAt)
    have hh : (fun z => G (Fin.cons 0 z)) = e ∘ (fun z => F (0, z)) ∘ e.symm := by
      funext z
      simp [G, Function.comp_def]
    rw [hh, hcomp.fderiv]
    exact LinearMap.det_conj _ e.toLinearEquiv
  have hVc : IsCompact (closure (e '' U)) := by
    rw [← show (e : E → (Fin n → ℝ)) '' closure U = closure (e '' U) from e.toHomeomorph.image_closure U]
    exact hc.image e.continuous
  have hb' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier (e '' U),
      G (Fin.cons t x) ≠ e y := by
    intro t ht x hx he
    rw [← show (e : E → (Fin n → ℝ)) '' frontier U = frontier (e '' U) from e.toHomeomorph.image_frontier U] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    apply hb t ht z hz
    apply e.injective
    simpa [G] using he
  let s' := s.map e.toEquiv.toEmbedding
  have hs' : ∀ x, x ∈ s' ↔ x ∈ e '' U ∧ G (Fin.cons 0 x) = e y := by
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      refine ⟨⟨z, (hs z).mp hz |>.1, rfl⟩, ?_⟩
      simp [G, (hs z).mp hz |>.2]
    · rintro ⟨⟨z, hz, rfl⟩, he⟩
      apply Finset.mem_map.mpr
      refine ⟨z, (hs z).mpr ⟨hz, ?_⟩, rfl⟩
      exact e.injective (by simpa [G] using he)
  have hd' : ∀ x ∈ s', (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det ≠ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    change (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e z)).det ≠ 0
    rw [hdet]
    exact hd z hz
  have hcount' : (∑ x ∈ s', (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0 := by
    change (∑ x ∈ s.map e.toEquiv.toEmbedding, _) ≠ 0
    rw [Finset.sum_map]
    change (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det then 1 else -1 : ℝ)) ≠ 0
    simpa only [hdet] using hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists G hG (e y) (e '' U)
    (e.toHomeomorph.isOpenMap _ hU) hVc hb' s' hs' hd' hcount'
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨z, hz, e.injective (by simpa [G] using he)⟩

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

/-- A regular perturbation at time zero can be propagated along an arbitrary
boundary-root-free smooth homotopy. The perturbation need not be equivariant
away from the initial time. -/
theorem regular_approximation_persists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F)
    (U : Set E) (hU : IsOpen U) (hc : IsCompact (closure U))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, F (t, x) ≠ 0)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : E → E, ContDiff ℝ ∞ g ∧
      (∀ x ∈ closure U, ‖g x - F (0, x)‖ < ε) ∧
      ∃ s : Finset E, (∀ x, x ∈ s ↔ x ∈ closure U ∧ g x = 0) ∧
        (∀ x ∈ s, (fderiv ℝ g x).det ≠ 0) ∧
        (∑ x ∈ s, (if 0 < (fderiv ℝ g x).det then 1 else -1 : ℝ)) ≠ 0) :
    ∃ x ∈ U, F (1, x) = 0 := by
  classical
  let P := Icc (0 : ℝ) 1 ×ˢ frontier U
  have hP : IsCompact P := isCompact_Icc.prod
    (hc.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  have hz : (0 : E) ∈ (F '' P)ᶜ := by
    rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, he⟩
    exact hb t ht x hx he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hP.image hF.continuous).isClosed.isOpen_compl 0 hz
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, ε ≤ ‖F (t, x)‖ := by
    intro t ht x hx
    by_contra hn
    have hmem : F (t, x) ∈ Metric.ball (0 : E) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hn
    exact hball hmem ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  obtain ⟨g, hg, hclose, s, hs, hd, hcount⟩ := happrox ε hε
  let G : ℝ × E → E := fun q => F q + (1 - q.1) • (g q.2 - F (0, q.2))
  have hG : ContDiff ℝ 2 G := hF.add
    ((contDiff_const.sub contDiff_fst).smul (((contDiff_infty.mp hg 2).comp contDiff_snd).sub
      (hF.comp (contDiff_const.prodMk contDiff_snd))))
  have hG0 : (fun x => G (0, x)) = g := by funext x; simp [G]
  have hG1 : (fun x => G (1, x)) = fun x => F (1, x) := by funext x; simp [G]
  have hGb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, G (t, x) ≠ 0 := by
    intro t ht x hx he
    have heq : F (t, x) = -((1 - t) • (g x - F (0, x))) := eq_neg_of_add_eq_zero_left he
    have hn : ‖F (t, x)‖ < ε := by
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      calc
        (1 - t) * ‖g x - F (0, x)‖ ≤ ‖g x - F (0, x)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
        _ < ε := hclose x (frontier_subset_closure hx)
    exact (not_lt_of_ge (hbound t ht x hx)) hn
  have hsU : ∀ x, x ∈ s ↔ x ∈ U ∧ G (0, x) = 0 := by
    intro x
    rw [hs, show G (0, x) = g x from congrFun hG0 x]
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨?_, he⟩
      by_contra hn
      have hxf : x ∈ frontier U := ⟨hx, by simpa only [hU.interior_eq] using hn⟩
      exact hGb 0 (by simp) x hxf (by rw [show G (0, x) = g x from congrFun hG0 x]; exact he)
    · rintro ⟨hx, he⟩; exact ⟨subset_closure hx, he⟩
  have hd' : ∀ x ∈ s, (fderiv ℝ (fun z => G (0, z)) x).det ≠ 0 := by rw [hG0]; exact hd
  have hcount' : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (0, z)) x).det then 1 else -1 : ℝ)) ≠ 0 := by
    rw [hG0]; exact hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists_finiteDimensional G hG 0 U hU hc hGb s hsU hd' hcount'
  exact ⟨x, hx, by simpa only [show G (1, x) = F (1, x) from congrFun hG1 x] using he⟩

/-- Localized nonsingular-exponent word-map roots cannot disappear under a
boundary-root-free smooth homotopy, even though the initial word map can have
singular roots. -/
theorem localized_word_root_persists {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (F : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)))
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ q, F (0, q) = splitWordMap w q)
    (U : Set ((Fin m → ℂ) × (Fin m → ℂ))) (hU : IsOpen U)
    (hc : IsCompact (closure U))
    (hUi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ closure U, (q.1, z • q.2) ∈ closure U)
    (h1 : (1, 0) ∈ U)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier U, F (t, x) ≠ 0) :
    ∃ x ∈ U, F (1, x) = 0 := by
  apply regular_approximation_persists F hF U hU hc hb
  intro ε hε
  simpa only [hF0] using word_exists_regularization_nonzero_count w hB
    (closure U) hc hUi (subset_closure h1) (closure U) hc (Subset.refl _) ε hε

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory

/-- Stokes localization in an arbitrary open subset of time times space.
The two slices may be different; no regularity of the moving boundary is used. -/
theorem jacobian_integral_moving_box {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, F y ∉ tsupport ρ)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (a b : Fin n → ℝ) (hab : a ≤ b)
    (hbox : ∀ t, {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} ⊆ Icc a b)
    (hside : ∀ i : Fin (n + 1), i ≠ 0 →
      ∀ x ∈ Icc ((Fin.cons t₀ a : Fin (n + 1) → ℝ) ∘ i.succAbove)
        ((Fin.cons t₁ b : Fin (n + 1) → ℝ) ∘ i.succAbove),
      i.insertNth ((Fin.cons t₁ b : Fin (n + 1) → ℝ) i) x ∉ C ∧
      i.insertNth ((Fin.cons t₀ a : Fin (n + 1) → ℝ) i) x ∉ C) :
    (∫ x in {x | (Fin.cons t₁ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det * ρ (F (Fin.cons t₁ x))) =
    ∫ x in {x | (Fin.cons t₀ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det * ρ (F (Fin.cons t₀ x)) := by
  classical
  let form := fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
    (fderiv ℝ F y)
  have hc : Disjoint (frontier C) (tsupport form) := by
    apply disjoint_left.mpr
    intro y hy hs
    exact hboundary y hy (tsupport_pullback_density_subset ρ F hF.continuous hs)
  obtain ⟨hd, hz⟩ := localized_closedForm form
    (differentiable_pullback_topForm _ (hρ.smul_const _) F hF)
    (extDeriv_pullback_topForm_eq_zero _ (hρ.smul_const _) F hF) C hC hc
  have htbox : (Fin.cons t₀ a : Fin (n + 1) → ℝ) ≤ Fin.cons t₁ b := by
    intro i
    exact Fin.cases ht (fun j => hab j) i
  have he := closedForm_opposite_faces (C.indicator form) hd hz
    (Fin.cons t₀ a) (Fin.cons t₁ b) htbox 0 (by
      intro i hi x hx
      obtain ⟨h₁, h₀⟩ := hside i hi x hx
      simp [formFlux, indicator_of_notMem h₁, indicator_of_notMem h₀])
  have hface (t : ℝ) (x : Fin n → ℝ) :
      formFlux (C.indicator form) 0 (Fin.cons t x) =
        {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C}.indicator
          (fun z => (fderiv ℝ (fun w => F (Fin.cons t w)) z).det *
          ρ (F (Fin.cons t z))) x := by
    by_cases hx : (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C
    · rw [indicator_of_mem (show x ∈ {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} from hx)]
      change (-1 : ℝ) ^ (0 : Fin (n + 1)).val *
        (C.indicator form) (Fin.cons t x) _ = _
      rw [indicator_of_mem hx]
      exact formFlux_pullback_first_face ρ F t x (hF.differentiable (by norm_num) _)
    · simp [formFlux, hx]
  have hins (t : ℝ) (x : Fin n → ℝ) :
      (0 : Fin (n + 1)).insertNth t x = (Fin.cons t x : Fin (n + 1) → ℝ) := by
    simp only [Fin.insertNth_zero, cast_eq]
  have hm (t : ℝ) : MeasurableSet {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} := by
    apply (hC.preimage _).measurableSet
    apply continuous_pi
    intro i
    exact Fin.cases continuous_const (fun j => continuous_apply j) i
  simpa only [Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, Fin.cons_zero,
    hins, hface, setIntegral_indicator (hm _),
    inter_eq_right.mpr (hbox _)] using he

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology

/-- Box-free moving-domain Stokes, with arbitrary open moving slices contained
in one bounded spatial set. -/
theorem jacobian_integral_moving {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, F y ∉ tsupport ρ)
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t : ℝ, Fin.cons t x ∈ C})
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    (∫ x in {x | (Fin.cons t₁ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det * ρ (F (Fin.cons t₁ x))) =
    ∫ x in {x | (Fin.cons t₀ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det * ρ (F (Fin.cons t₀ x)) := by
  obtain ⟨R, hR, hbound⟩ := hCb.exists_pos_norm_lt
  have hcoord (t : ℝ) (x : Fin n → ℝ) (hx : Fin.cons t x ∈ C) (i : Fin n) : |x i| < R :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
      (hbound x ⟨t, hx⟩)
  have hout (y : Fin (n + 1) → ℝ) (j : Fin n)
      (hj : y j.succ = R ∨ y j.succ = -R) : y ∉ C := by
    intro hy
    have hh := hcoord (y 0) (Fin.tail y) (by simpa only [Fin.cons_self_tail] using hy) j
    change |y j.succ| < R at hh
    rcases hj with hj | hj
    · rw [hj, abs_of_pos hR] at hh; exact lt_irrefl _ hh
    · rw [hj, abs_neg, abs_of_pos hR] at hh; exact lt_irrefl _ hh
  apply jacobian_integral_moving_box ρ hρ F hF C hC hboundary t₀ t₁ ht
    (fun _ => -R) (fun _ => R) (fun _ => by linarith)
  · intro t x hx
    constructor <;> intro i
    · exact (abs_lt.mp (hcoord t x hx i)).1.le
    · exact (abs_lt.mp (hcoord t x hx i)).2.le
  · intro i hi x _
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    constructor
    · apply hout _ j
      left
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]
    · apply hout _ j
      right
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]

/-- Smooth time saturation reduces the collar hypothesis to the actual time
interval even for moving open domains. -/
theorem jacobian_integral_moving_interval {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, y 0 ∈ Icc (0 : ℝ) 1 → F y ∉ tsupport ρ)
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ C}) :
    (∫ x in {x | (Fin.cons 1 x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons 1 z)) x).det * ρ (F (Fin.cons 1 x))) =
    ∫ x in {x | (Fin.cons 0 x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det * ρ (F (Fin.cons 0 x)) := by
  let T : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => Fin.cons (Real.smoothTransition (y 0)) (Fin.tail y)
  have hT : ContDiff ℝ 2 T := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 0)
    · exact contDiff_apply ℝ ℝ j.succ
  have hb : ∀ y ∈ frontier (T ⁻¹' C), (F ∘ T) y ∉ tsupport ρ := by
    intro y hy
    exact hboundary (T y) (hT.continuous.frontier_preimage_subset C hy)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hbound : Bornology.IsBounded {x : Fin n → ℝ | ∃ t : ℝ, Fin.cons t x ∈ T ⁻¹' C} := by
    apply hCb.subset
    rintro x ⟨t, ht⟩
    exact ⟨Real.smoothTransition t, ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ht⟩
  have he := jacobian_integral_moving ρ hρ (F ∘ T) (hF.comp hT) (T ⁻¹' C)
    (hC.preimage hT.continuous) hb hbound 0 1 zero_le_one
  simpa only [T, Function.comp_apply, mem_preimage, Fin.cons_zero, Fin.tail_cons,
    Real.smoothTransition.zero, Real.smoothTransition.one] using he

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology

/-- A nonzero signed count survives an arbitrary moving open set. The compact
boundary slab hypothesis is satisfied by the fixed annulus in the quaternion
application; no boundary triangulation or regular-value hypothesis is used
along the homotopy. -/
theorem regular_count_persists_moving {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (y : Fin n → ℝ) (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (Fin.cons 0 x : Fin (n + 1) → ℝ) ∈ C}))
    (hc₁ : IsCompact (closure {x | (Fin.cons 1 x : Fin (n + 1) → ℝ) ∈ C}))
    (hcB : IsCompact {q | q ∈ frontier C ∧ q 0 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ C})
    (hb : ∀ q ∈ frontier C, q 0 ∈ Icc (0 : ℝ) 1 → F q ≠ y)
    (s : Finset (Fin n → ℝ))
    (hs : ∀ x, x ∈ s ↔ Fin.cons 0 x ∈ C ∧ F (Fin.cons 0 x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) : ∃ x, Fin.cons 1 x ∈ C ∧ F (Fin.cons 1 x) = y := by
  classical
  by_contra hno
  have hno' : ∀ x, Fin.cons 1 x ∈ C → F (Fin.cons 1 x) ≠ y := by simpa using hno
  let U : ℝ → Set (Fin n → ℝ) := fun t => {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C}
  let f₀ := fun x => F (Fin.cons 0 x)
  let f₁ := fun x => F (Fin.cons 1 x)
  have hcons (t : ℝ) : ContDiff ℝ 2 (fun x : Fin n → ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    exact Fin.cases contDiff_const (fun j => contDiff_apply ℝ ℝ j) i
  have hU (t : ℝ) : IsOpen (U t) := hC.preimage (hcons t).continuous
  have hfront (t : ℝ) : frontier (U t) ⊆
      (fun x : Fin n → ℝ => Fin.cons t x) ⁻¹' frontier C :=
    (hcons t).continuous.frontier_preimage_subset C
  have hf₀ : ContDiff ℝ 1 f₀ := (hF.comp (hcons 0)).of_le (by norm_num)
  have hf₁ : Continuous f₁ := (hF.comp (hcons 1)).continuous
  obtain ⟨N, hN, hyN, hsign⟩ := regular_signed_count_neighborhood volume f₀ hf₀ y (U 0)
    (hU 0) hc₀ (fun x hx => hb _ (hfront 0 hx) (by simp)) s hs hd
  let K := F '' {q | q ∈ frontier C ∧ q 0 ∈ Icc (0 : ℝ) 1}
  have hK : IsCompact K := hcB.image hF.continuous
  have hyK : y ∉ K := by
    rintro ⟨q, ⟨hq, ht⟩, he⟩
    exact hb q hq ht he
  have hy₁ : y ∉ f₁ '' closure (U 1) := by
    rintro ⟨x, hx, he⟩
    by_cases hxU : x ∈ U 1
    · exact hno' x hxU he
    · have hxf : x ∈ frontier (U 1) := ⟨hx, by simpa only [(hU 1).interior_eq] using hxU⟩
      exact hb _ (hfront 1 hxf) (by simp) he
  let M := N \ (K ∪ f₁ '' closure (U 1))
  have hM : IsOpen M := hN.sdiff (hK.isClosed.union (hc₁.image hf₁).isClosed)
  have hyM : y ∈ M := ⟨hyN, fun h => h.elim hyK hy₁⟩
  obtain ⟨ρ, hρ, _, hρM, hunit⟩ := exists_normalized_smooth_bump volume y M hM hyM
  have hρN : Function.support ρ ⊆ N := fun z hz => (hρM (subset_tsupport ρ hz)).1
  have hval : jacobianIntegral volume f₀ (U 0) ρ =
      ∑ x ∈ s, (if 0 < (fderiv ℝ f₀ x).det then 1 else -1) :=
    hsign ρ hρ.continuous hρN hunit
  have hcollar : ∀ q ∈ frontier C, q 0 ∈ Icc (0 : ℝ) 1 → F q ∉ tsupport ρ := by
    intro q hq ht hsup
    exact (hρM hsup).2 (Or.inl ⟨q, ⟨hq, ht⟩, rfl⟩)
  have hinv := jacobian_integral_moving_interval ρ (hρ.differentiable (by simp)) F hF C hC hcollar hCb
  have hzero : jacobianIntegral volume f₁ (U 1) ρ = 0 := by
    apply jacobianIntegral_eq_zero_of_no_preimage
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hsup
    exact (hρM hsup).2 (Or.inr ⟨x, subset_closure hx, rfl⟩)
  apply hcount
  exact hval.symm.trans (hinv.symm.trans hzero)

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coordinate-free moving-domain nonzero-count persistence. -/
theorem regular_count_persists_moving_finiteDimensional
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F) (y : E)
    (C : Set (ℝ × E)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ y)
    (s : Finset E) (hs : ∀ x, x ∈ s ↔ (0, x) ∈ C ∧ F (0, x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (0, z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (0, z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) : ∃ x, (1, x) ∈ C ∧ F (1, x) = y := by
  classical
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ E).equivFunL
  let H : (ℝ × E) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e).trans (Fin.consEquivL ℝ (fun _ => ℝ))
  let G : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun q => e (F (H.symm q))
  let D := H.symm ⁻¹' C
  have hH (t : ℝ) (x : E) : H (t, x) = Fin.cons t (e x) := rfl
  have hHi (t : ℝ) (x : Fin n → ℝ) : H.symm (Fin.cons t x) = (t, e.symm x) := by
    apply H.injective
    rw [H.apply_symm_apply, hH, e.apply_symm_apply]
  have hG : ContDiff ℝ 2 G := e.contDiff.comp (hF.comp H.symm.contDiff)
  have hdet (x : E) :
      (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det =
      (fderiv ℝ (fun z => F (0, z)) x).det := by
    have h₀ : DifferentiableAt ℝ (fun z => F (0, z)) x :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
    have h₀' : HasFDerivAt (fun z => F (0, z))
        (fderiv ℝ (fun z => F (0, z)) x) (e.symm (e x)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using h₀.hasFDerivAt
    have hcomp := e.hasFDerivAt.comp (e x) (h₀'.comp (e x) e.symm.hasFDerivAt)
    have hh : (fun z => G (Fin.cons 0 z)) = e ∘ (fun z => F (0, z)) ∘ e.symm := by
      funext z; simp only [G, hHi, Function.comp_def]
    rw [hh, hcomp.fderiv]
    exact LinearMap.det_conj _ e.toLinearEquiv
  have hslice (t : ℝ) : {x : Fin n → ℝ | Fin.cons t x ∈ D} = e '' {x | (t, x) ∈ C} := by
    ext x
    change H.symm (Fin.cons t x) ∈ C ↔ _
    rw [hHi]
    constructor
    · intro hx; exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩; simpa only [ContinuousLinearEquiv.symm_apply_apply, mem_ofPred_eq] using hz
  have hcompact (t : ℝ) (ht : IsCompact (closure {x : E | (t, x) ∈ C})) :
      IsCompact (closure {x : Fin n → ℝ | Fin.cons t x ∈ D}) := by
    rw [hslice, ← show (e : E → (Fin n → ℝ)) '' closure {x | (t, x) ∈ C} = closure (e '' {x | (t, x) ∈ C}) from e.toHomeomorph.image_closure _]
    exact ht.image e.continuous
  have hfront : frontier D = H.symm ⁻¹' frontier C := by
    exact (H.symm.toHomeomorph.preimage_frontier C).symm
  have hboundary : {q : Fin (n + 1) → ℝ | q ∈ frontier D ∧ q 0 ∈ Icc (0 : ℝ) 1} =
      H '' {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1} := by
    ext q
    rw [hfront]
    constructor
    · rintro ⟨hq, ht⟩
      refine ⟨H.symm q, ⟨hq, ?_⟩, H.apply_symm_apply q⟩
      exact ht
    · rintro ⟨z, ⟨hz, ht⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
      · exact ht
  have hbounded : {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ D} =
      e '' {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C} := by
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      have hx' : x ∈ e '' {z | (t, z) ∈ C} := by rw [← hslice]; exact hx
      obtain ⟨z, hz, rfl⟩ := hx'
      exact ⟨z, ⟨t, ht, hz⟩, rfl⟩
    · rintro ⟨z, ⟨t, ht, hz⟩, rfl⟩
      exact ⟨t, ht, by change e z ∈ {x | Fin.cons t x ∈ D}; rw [hslice]; exact ⟨z, hz, rfl⟩⟩
  let s' := s.map e.toEquiv.toEmbedding
  have hs' : ∀ x, x ∈ s' ↔ Fin.cons 0 x ∈ D ∧ G (Fin.cons 0 x) = e y := by
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      change H.symm (Fin.cons 0 (e z)) ∈ C ∧ e (F (H.symm (Fin.cons 0 (e z)))) = e y
      rw [hHi, e.symm_apply_apply]
      exact ⟨((hs z).mp hz).1, congrArg e ((hs z).mp hz).2⟩
    · rintro ⟨hx, he⟩
      refine Finset.mem_map.mpr ⟨e.symm x, (hs _).mpr ⟨?_, ?_⟩, e.apply_symm_apply x⟩
      · simpa only [D, mem_preimage, hHi] using hx
      · apply e.injective; simpa only [G, hHi] using he
  have hd' : ∀ x ∈ s', (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det ≠ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    change (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e z)).det ≠ 0
    rw [hdet]; exact hd z hz
  have hcount' : (∑ x ∈ s', (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0 := by
    change (∑ x ∈ s.map e.toEquiv.toEmbedding, _) ≠ 0
    rw [Finset.sum_map]
    change (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det then 1 else -1 : ℝ)) ≠ 0
    simpa only [hdet] using hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists_moving G hG (e y) D
    (hC.preimage H.symm.continuous) (hcompact 0 hc₀) (hcompact 1 hc₁)
    (by rw [hboundary]; exact hcB.image H.continuous)
    (by rw [hbounded]; exact e.lipschitzWith.isBounded_image hCb)
    (by
      intro q hq ht heq
      apply hb (H.symm q) (by rw [hfront] at hq; exact hq) ht
      exact e.injective heq) s' hs' hd' hcount'
  exact ⟨e.symm x, by simpa only [D, mem_preimage, hHi] using hx,
    e.injective (by simpa only [G, hHi] using he)⟩
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Arbitrarily small regular approximations at the initial slice suffice for
moving-domain continuation. Uniform closeness is requested on the spatial
projection of the boundary slab, not on an assumed fixed isolating domain. -/
theorem regular_approximation_persists_moving
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F)
    (C : Set (ℝ × E)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0)
    (L : Set E) (hLB : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → q.2 ∈ L)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : E → E, ContDiff ℝ ∞ g ∧
      (∀ x ∈ L, ‖g x - F (0, x)‖ < ε) ∧
      ∃ s : Finset E, (∀ x, x ∈ s ↔ x ∈ closure {z | (0, z) ∈ C} ∧ g x = 0) ∧
        (∀ x ∈ s, (fderiv ℝ g x).det ≠ 0) ∧
        (∑ x ∈ s, (if 0 < (fderiv ℝ g x).det then 1 else -1 : ℝ)) ≠ 0) :
    ∃ x, (1, x) ∈ C ∧ F (1, x) = 0 := by
  classical
  let P := {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1}
  have hz : (0 : E) ∈ (F '' P)ᶜ := by
    rintro ⟨q, ⟨hq, ht⟩, he⟩
    exact hb q hq ht he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hcB.image hF.continuous).isClosed.isOpen_compl 0 hz
  have hbound : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → ε ≤ ‖F q‖ := by
    intro q hq ht
    by_contra hn
    have hmem : F q ∈ Metric.ball (0 : E) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hn
    exact hball hmem ⟨q, ⟨hq, ht⟩, rfl⟩
  obtain ⟨g, hg, hclose, s, hs, hd, hcount⟩ := happrox ε hε
  let G : ℝ × E → E := fun q => F q + (1 - q.1) • (g q.2 - F (0, q.2))
  have hG : ContDiff ℝ 2 G := hF.add
    ((contDiff_const.sub contDiff_fst).smul (((contDiff_infty.mp hg 2).comp contDiff_snd).sub
      (hF.comp (contDiff_const.prodMk contDiff_snd))))
  have hG0 : (fun x => G (0, x)) = g := by funext x; simp [G]
  have hG1 : (fun x => G (1, x)) = fun x => F (1, x) := by funext x; simp [G]
  have hGb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → G q ≠ 0 := by
    intro q hq ht he
    have heq : F q = -((1 - q.1) • (g q.2 - F (0, q.2))) := eq_neg_of_add_eq_zero_left he
    have hn : ‖F q‖ < ε := by
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      calc
        (1 - q.1) * ‖g q.2 - F (0, q.2)‖ ≤ ‖g q.2 - F (0, q.2)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
        _ < ε := hclose q.2 (hLB q hq ht)
    exact (not_lt_of_ge (hbound q hq ht)) hn
  have hU : IsOpen {x : E | (0, x) ∈ C} := hC.preimage (continuous_const.prodMk continuous_id)
  have hfront : frontier {x : E | (0, x) ∈ C} ⊆ (fun x : E => ((0 : ℝ), x)) ⁻¹' frontier C :=
    (continuous_const.prodMk continuous_id).frontier_preimage_subset C
  have hsU : ∀ x, x ∈ s ↔ (0, x) ∈ C ∧ G (0, x) = 0 := by
    intro x
    rw [hs, show G (0, x) = g x from congrFun hG0 x]
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨?_, he⟩
      by_contra hn
      have hxf : x ∈ frontier {z : E | (0, z) ∈ C} :=
        ⟨hx, by simpa only [hU.interior_eq, mem_ofPred_eq] using hn⟩
      exact hGb (0, x) (hfront hxf) (by simp)
        (by rw [show G (0, x) = g x from congrFun hG0 x]; exact he)
    · rintro ⟨hx, he⟩; exact ⟨subset_closure hx, he⟩
  have hd' : ∀ x ∈ s, (fderiv ℝ (fun z => G (0, z)) x).det ≠ 0 := by rw [hG0]; exact hd
  have hcount' : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (0, z)) x).det then 1 else -1 : ℝ)) ≠ 0 := by
    rw [hG0]; exact hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists_moving_finiteDimensional G hG 0 C hC hc₀ hc₁ hcB hCb hGb s hsU hd' hcount'
  exact ⟨x, hx, by simpa only [show G (1, x) = F (1, x) from congrFun hG1 x] using he⟩

/-- Full localized word-root persistence for moving open sets. Contains the
singular pure-word initial maps used in the manuscript's finite-quotient step. -/
theorem localized_word_root_persists_moving {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (F : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)))
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ q, F (0, q) = splitWordMap w q)
    (C : Set (ℝ × ((Fin m → ℂ) × (Fin m → ℂ)))) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hUi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ closure {x | (0, x) ∈ C},
      (q.1, z • q.2) ∈ closure {x | (0, x) ∈ C})
    (h1 : (0, (1, 0)) ∈ C)
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0) :
    ∃ x, (1, x) ∈ C ∧ F (1, x) = 0 := by
  let K := closure {x | (0, x) ∈ C}
  let L := K ∪ Prod.snd '' {q | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1}
  have hL : IsCompact L := hc₀.union (hcB.image continuous_snd)
  apply regular_approximation_persists_moving F hF C hC hc₀ hc₁ hcB hCb hb L
    (fun q hq ht => Or.inr ⟨q, ⟨hq, ht⟩, rfl⟩)
  intro ε hε
  simpa only [hF0] using word_exists_regularization_nonzero_count w hB
    K hc₀ hUi (subset_closure h1) L hL subset_union_left ε hε
end EilenbergGanea

end

end OAI
