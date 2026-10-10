import OAI.Topology.EilenbergGanea.IntegralDegree
import OAI.Topology.EilenbergGanea.UnitaryWords

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

/-- A concrete sublevel version of localized degree. The only root isolation
conditions are a uniform radial bound and exclusion of the threshold; no
regularity of any root or of the sublevel boundary is assumed. -/
theorem localized_word_root_sublevel {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (F : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)))
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ q, F (0, q) = splitWordMap w q)
    (h : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ℝ) (hh : Continuous h)
    (δ R : ℝ) (hR : ‖((1 : Fin m → ℂ), (0 : Fin m → ℂ))‖ < R)
    (h1 : h (0, (1, 0)) < δ)
    (hi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q, h (0, (q.1, z • q.2)) = h (0, q))
    (hbound : ∀ q, q.1 ∈ Icc (0 : ℝ) 1 → F q = 0 → ‖q.2‖ < R)
    (hiso : ∀ q, q.1 ∈ Icc (0 : ℝ) 1 → F q = 0 → h q ≠ δ) :
    ∃ x, F (1, x) = 0 ∧ h (1, x) < δ := by
  let E := (Fin m → ℂ) × (Fin m → ℂ)
  let C : Set (ℝ × E) := {q | ‖q.2‖ < R ∧ h q < δ}
  have hC : IsOpen C := (isOpen_lt continuous_snd.norm continuous_const).inter
    (isOpen_lt hh continuous_const)
  have hcl : closure C ⊆ {q | ‖q.2‖ ≤ R ∧ h q ≤ δ} :=
    closure_minimal (fun _ hq => ⟨hq.1.le, hq.2.le⟩)
      ((isClosed_le continuous_snd.norm continuous_const).inter (isClosed_le hh continuous_const))
  have hslice (t : ℝ) : Bornology.IsBounded {x : E | (t, x) ∈ C} := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.1.le)
  have hBcompact : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1} := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
      (isClosed_frontier.inter (isClosed_Icc.preimage continuous_fst))
    intro q hq
    refine ⟨hq.2, ?_⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (hcl (frontier_subset_closure hq.1)).1)
  have hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C} := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    rintro x ⟨t, _, hx⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.1.le)
  have hUi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ closure {x : E | (0, x) ∈ C},
      (q.1, z • q.2) ∈ closure {x : E | (0, x) ∈ C} := by
    intro z hz
    have hmaps : MapsTo (fun q : E => (q.1, z • q.2)) {x | (0, x) ∈ C} {x | (0, x) ∈ C} := by
      intro q hq
      refine ⟨?_, ?_⟩
      · have hn : ‖(q.1, z • q.2)‖ = ‖q‖ := by
          change max ‖q.1‖ ‖z • q.2‖ = max ‖q.1‖ ‖q.2‖
          rw [norm_smul, hz, one_mul]
        simpa only [hn] using hq.1
      · simpa only [hi z hz q] using hq.2
    have hr : Continuous (fun q : E => (q.1, z • q.2)) := by fun_prop
    exact hmaps.closure_of_continuousOn hr.continuousOn
  have hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0 := by
    intro q hq ht hf
    have hhδ : h q < δ := lt_of_le_of_ne (hcl (frontier_subset_closure hq)).2 (hiso q ht hf)
    have hqC : q ∈ C := ⟨hbound q ht hf, hhδ⟩
    exact hq.2 (by simpa only [hC.interior_eq] using hqC)
  obtain ⟨x, hx, he⟩ := localized_word_root_persists_moving w hB F hF hF0 C hC
    (hslice 0).isCompact_closure (hslice 1).isCompact_closure hBcompact hCb hUi ⟨hR, h1⟩ hb
  exact ⟨x, he, hx.2⟩
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

/-- Word evaluation with a fixed alphabet of coefficient letters and a finite
alphabet of unknowns. Coefficients may vary smoothly with a real parameter. -/
def coefficientWordMap {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → SU2)) : Fin d → SU2 :=
  fun i => FreeGroup.lift (Sum.elim (a q.1) q.2) (w i)

def eraseCoefficients {ι : Type*} {m : ℕ} : FreeGroup (ι ⊕ Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

theorem coefficientWordMap_initial {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (x : Fin m → SU2) :
    coefficientWordMap w a (0, x) = fun i => FreeGroup.lift x (eraseCoefficients (w i)) := by
  have he : FreeGroup.lift (Sum.elim (a 0) x) = (FreeGroup.lift x).comp eraseCoefficients := by
    apply FreeGroup.ext_hom
    intro i
    cases i with
    | inl i => simp [eraseCoefficients, ha]
    | inr i => simp [eraseCoefficients]
  funext i
  exact congrArg (fun f : FreeGroup (ι ⊕ Fin m) →* SU2 => f (w i)) he

/-- The same conjugation-invariant radial cutoff handles arbitrary coefficient
words, and does not create roots on the coordinate hyperplanes. -/
theorem radialCutoff_family_smooth {m : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × (Fin m → ℍ) → V)
    (hf : ∀ q, (∀ i, q.2 i ≠ 0) → ContDiffAt ℝ ∞ f q) :
    ContDiff ℝ ∞ (fun q => radialCutoff q.2 • f q) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ∀ i, q.2 i ≠ 0
  · exact (radialCutoff_contDiff.comp contDiff_snd).contDiffAt.smul (hf q hq)
  · push Not at hq
    obtain ⟨i, hi⟩ := hq
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × (Fin m → ℍ) => (0 : V)) q).congr_of_eventuallyEq
    have he : ∀ᶠ p in 𝓝 q, radialCutoff p.2 = 0 :=
      continuous_snd.continuousAt (radialCutoff_eventually_zero q.2 i hi)
    filter_upwards [he] with p hp
    simp only [hp, zero_smul]

theorem coefficientWordMap_normalized_smoothAt {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ)))
    (q : ℝ × (Fin m → ℍ)) (hq : ∀ i, q.2 i ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin m → ℍ) =>
      fun i => (coefficientWordMap w a (p.1, fun j => normalizeQuaternion (p.2 j)) i : ℍ)) q := by
  apply contDiffAt_pi.mpr
  intro i
  refine freeGroup_lift_coe_contDiffAt (w i) q
    (fun parameter => Sum.elim (a parameter.1)
      (fun index => normalizeQuaternion (parameter.2 index))) ?_
  intro j
  cases j with
  | inl j => exact ((ha j).comp contDiff_fst).contDiffAt
  | inr j =>
      change ContDiffAt ℝ ∞ (fun p : ℝ × (Fin m → ℍ) => (normalizeQuaternion (p.2 j) : ℍ)) q
      exact (normalizeQuaternion_coe_contDiffAt (hq j)).comp (f := fun p : ℝ × (Fin m → ℍ) => p.2 j) q
        ((contDiff_apply ℝ ℍ j).comp contDiff_snd).contDiffAt

def radialCoefficientWordMap {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin m → ℍ :=
  fun i => ‖q.2 i‖ • (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i : ℍ)

def smoothRadialCoefficientWordMap {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin m → ℍ :=
  radialCutoff q.2 • radialCoefficientWordMap w a q

theorem smoothRadialCoefficientWordMap_smooth {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ))) :
    ContDiff ℝ ∞ (smoothRadialCoefficientWordMap w a) := by
  apply radialCutoff_family_smooth
  intro q hq
  apply contDiffAt_pi.mpr
  intro i
  exact (((contDiff_apply ℝ ℍ i).comp contDiff_snd).contDiffAt.norm ℝ (hq i)).smul
    ((contDiffAt_pi.mp (coefficientWordMap_normalized_smoothAt w a ha q hq)) i)

@[simp] theorem radialCoefficientWordMap_norm {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) (i : Fin m) :
    ‖radialCoefficientWordMap w a q i‖ = ‖q.2 i‖ := by
  have h := (quaternion_mem_unitary_iff _).mp
    (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i).property
  simp [radialCoefficientWordMap, norm_smul, h]

theorem radialCoefficientWordMap_eq_one_iff {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : radialCoefficientWordMap w a q = 1 ↔
      (∀ i, ‖q.2 i‖ = 1) ∧ coefficientWordMap w a
        (q.1, fun j => normalizeQuaternion (q.2 j)) = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : ‖q.2 i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [radialCoefficientWordMap_norm, Pi.one_apply, norm_one] using he
    refine ⟨hn, ?_⟩
    funext i
    apply Subtype.ext
    have he := congrFun h i
    simpa [radialCoefficientWordMap, hn] using he
  · rintro ⟨hn, hw⟩
    funext i
    simp [radialCoefficientWordMap, hn, hw]

theorem smoothRadialCoefficientWordMap_eq_one_iff {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : smoothRadialCoefficientWordMap w a q = 1 ↔
      (∀ i, ‖q.2 i‖ = 1) ∧ coefficientWordMap w a
        (q.1, fun j => normalizeQuaternion (q.2 j)) = 1 := by
  rw [← radialCoefficientWordMap_eq_one_iff]
  constructor
  · intro h
    have hn (i : Fin m) : radialCutoff q.2 * ‖q.2 i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [smoothRadialCoefficientWordMap, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (radialCutoff_nonneg q.2), radialCoefficientWordMap_norm, Pi.one_apply, norm_one] using he
    have hlarge (i : Fin m) : 1 ≤ ‖q.2 i‖ := by
      have hle := mul_le_mul_of_nonneg_right (radialCutoff_le_one q.2) (norm_nonneg (q.2 i))
      rw [hn i, one_mul] at hle
      exact hle
    simpa only [smoothRadialCoefficientWordMap, radialCutoff_eq_one q.2 hlarge, one_smul] using h
  · intro h
    have hn := (radialCoefficientWordMap_eq_one_iff w a q).mp h
    simp only [smoothRadialCoefficientWordMap, radialCutoff_eq_one q.2 (fun i => (hn.1 i).ge), one_smul, h]

theorem smoothRadialCoefficientWordMap_initial {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (x : Fin m → ℍ) :
    smoothRadialCoefficientWordMap w a (0, x) =
      smoothRadialWordMap (fun i => eraseCoefficients (w i)) x := by
  unfold smoothRadialCoefficientWordMap smoothRadialWordMap
  congr 1
  funext i
  dsimp only [radialCoefficientWordMap, radialWordMap]
  rw [coefficientWordMap_initial w a ha]
  rfl
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

def cutoffCoefficientProducts {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : Fin d → ℍ :=
  radialCutoff q.2 • fun i =>
    (coefficientWordMap w a (q.1, fun j => normalizeQuaternion (q.2 j)) i : ℍ)

theorem cutoffCoefficientProducts_smooth {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ))) :
    ContDiff ℝ ∞ (cutoffCoefficientProducts w a) :=
  radialCutoff_family_smooth _ (coefficientWordMap_normalized_smoothAt w a ha)

theorem cutoffCoefficientProducts_unitary {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (t : ℝ) (x : Fin m → SU2) :
    cutoffCoefficientProducts w a (t, fun i => (x i : ℍ)) =
      fun i => (coefficientWordMap w a (t, x) i : ℍ) := by
  have hn (i : Fin m) : ‖(x i : ℍ)‖ = 1 := (quaternion_mem_unitary_iff _).mp (x i).property
  simp only [cutoffCoefficientProducts, radialCutoff_eq_one _ (fun i => (hn i).ge), one_smul,
    normalizeQuaternion_unitary]
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

 theorem quaternionConjugate_sub (a : SU2) (q r : ℍ) :
    quaternionConjugate a (q - r) = quaternionConjugate a q - quaternionConjugate a r := by
  simp only [quaternionConjugate, mul_sub, sub_mul]

 theorem coefficientWordMap_initial_conjugate {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → SU2) :
    coefficientWordMap w a (0, fun i => b * x i * b⁻¹) =
      fun i => b * coefficientWordMap w a (0, x) i * b⁻¹ := by
  rw [coefficientWordMap_initial w a ha, coefficientWordMap_initial w a ha]
  have he : FreeGroup.lift (fun i => b * x i * b⁻¹) =
      (MulAut.conj b).toMonoidHom.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  funext i
  rw [he]
  rfl

 theorem cutoffCoefficientProducts_initial_conjugate {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → ℍ) :
    cutoffCoefficientProducts w a (0, fun i => quaternionConjugate b (x i)) =
      fun i => quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) := by
  funext i
  simp only [cutoffCoefficientProducts, radialCutoff, quaternionConjugate_norm,
    normalizeQuaternion_conjugate, coefficientWordMap_initial_conjugate w a ha,
    Pi.smul_apply, quaternionConjugate_smul, quaternionConjugate_coe]

 theorem cutoffCoefficientProducts_initial_size_invariant {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → ℍ) :
    ‖cutoffCoefficientProducts w a (0, fun i => quaternionConjugate b (x i)) - 1‖ =
      ‖cutoffCoefficientProducts w a (0, x) - 1‖ := by
  rw [cutoffCoefficientProducts_initial_conjugate w a ha]
  have hn (i : Fin d) : ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) - 1‖ =
      ‖cutoffCoefficientProducts w a (0, x) i - 1‖ := by
    calc
      _ = ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i - 1)‖ := by rw [quaternionConjugate_sub, quaternionConjugate_one]
      _ = _ := quaternionConjugate_norm _ _
  have hnn (i : Fin d) : ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) - 1‖₊ =
      ‖cutoffCoefficientProducts w a (0, x) i - 1‖₊ := NNReal.eq (hn i)
  simp only [Pi.norm_def, Pi.sub_apply, Pi.one_apply, hnn]

/-- Finite-word-system solvability with an actual distinguished-word sublevel
isolator. Arbitrarily singular initial word roots are allowed. -/
theorem coefficient_word_sublevel_solvable {ι : Type*} {m d : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (ρ : Fin d → FreeGroup (ι ⊕ Fin m))
    (a : ℝ → ι → SU2) (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ)))
    (ha0 : ∀ i, a 0 i = 1)
    (hB : (exponentMatrix (fun i => eraseCoefficients (w i))).det ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Fin m → SU2,
      coefficientWordMap w a (t, x) = 1 →
      ‖(fun i => (coefficientWordMap ρ a (t, x) i : ℍ)) - 1‖ ≠ δ) :
    ∃ x : Fin m → SU2, coefficientWordMap w a (1, x) = 1 ∧
      ‖(fun i => (coefficientWordMap ρ a (1, x) i : ℍ)) - 1‖ < δ := by
  let E := (Fin m → ℂ) × (Fin m → ℂ)
  let e : (Fin m → ℍ) ≃L[ℝ] E := quaternionTupleCoordinates
  let H : ℝ × E → ℝ × (Fin m → ℍ) := fun q => (q.1, e.symm q.2)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)
  let F : ℝ × E → E := fun q => e (smoothRadialCoefficientWordMap w a (H q)) - (1, 0)
  let h : ℝ × E → ℝ := fun q => ‖cutoffCoefficientProducts ρ a (H q) - 1‖
  have hF : ContDiff ℝ 2 F := contDiff_infty.mp
    ((e.contDiff.comp ((smoothRadialCoefficientWordMap_smooth w a ha).comp hH)).sub contDiff_const) 2
  have hF0 : ∀ q, F (0, q) = splitWordMap (fun i => eraseCoefficients (w i)) q := by
    intro q
    dsimp only [F, H]
    rw [smoothRadialCoefficientWordMap_initial w a ha0]
    rfl
  have hh : Continuous h := (((cutoffCoefficientProducts_smooth ρ a ha).comp hH).continuous.sub continuous_const).norm
  have he1 : e (1 : Fin m → ℍ) = (1, 0) := by
    change quaternionTupleCoordinates
      (fun _ : Fin m => Quaternion.ofComplex (1 : ℂ)) = _
    exact quaternionTupleCoordinates_fixed 1
  have hroot (q : ℝ × E) (hq : F q = 0) :
      (∀ i, ‖e.symm q.2 i‖ = 1) ∧
      coefficientWordMap w a (q.1, fun i => normalizeQuaternion (e.symm q.2 i)) = 1 := by
    apply (smoothRadialCoefficientWordMap_eq_one_iff w a (H q)).mp
    apply e.injective
    rw [he1]
    exact sub_eq_zero.mp hq
  have hnorm (q : ℝ × E) (hq : F q = 0) : ‖q.2‖ ≤ ‖e.toContinuousLinearMap‖ := by
    have hle : ‖e.symm q.2‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      (fun i => (hroot q hq).1 i |>.le)
    calc
      ‖q.2‖ = ‖e (e.symm q.2)‖ := by rw [e.apply_symm_apply]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm q.2‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ := mul_le_of_le_one_right (norm_nonneg e.toContinuousLinearMap) hle
  have hunit (q : ℝ × E) (hq : F q = 0) :
      (fun i => ((normalizeQuaternion (e.symm q.2 i) : SU2) : ℍ)) = e.symm q.2 := by
    funext i
    have hn := (hroot q hq).1 i
    rw [normalizeQuaternion_coe_of_ne_zero (by intro hz; simp [hz] at hn), hn, inv_one, one_smul]
  have hsizeroot (q : ℝ × E) (hq : F q = 0) :
      h q = ‖(fun i => (coefficientWordMap ρ a
        (q.1, fun j => normalizeQuaternion (e.symm q.2 j)) i : ℍ)) - 1‖ := by
    dsimp only [h, H]
    conv_lhs => rw [← hunit q hq, cutoffCoefficientProducts_unitary]
  have hi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q : E, h (0, (q.1, z • q.2)) = h (0, q) := by
    intro z hz q
    obtain ⟨c, hc⟩ := circle_exists_square_root z hz
    have heq : e.symm (q.1, z • q.2) =
        fun i => quaternionConjugate (circleQuaternion c) (e.symm q i) := by
      apply e.injective
      rw [e.apply_symm_apply, quaternionTupleCoordinates_conjCircle, hc, e.apply_symm_apply]
    dsimp only [h, H]
    rw [heq]
    exact cutoffCoefficientProducts_initial_size_invariant ρ a ha0 _ _
  have h1 : h (0, (1, 0)) < δ := by
    have he : e.symm (1, 0) = 1 := by rw [← he1, e.symm_apply_apply]
    have hp : coefficientWordMap ρ a (0, (1 : Fin m → SU2)) = 1 := by
      rw [coefficientWordMap_initial ρ a ha0]
      have hl : FreeGroup.lift (1 : Fin m → SU2) = 1 := by
        apply FreeGroup.ext_hom
        intro i
        simp
      funext i
      rw [hl]
      rfl
    dsimp only [h, H]
    rw [he]
    have hco : (1 : Fin m → ℍ) = fun i => ((1 : Fin m → SU2) i : ℍ) := rfl
    rw [hco, cutoffCoefficientProducts_unitary, hp]
    change ‖(1 : Fin d → ℍ) - 1‖ < δ
    simpa only [sub_self, norm_zero] using hδ
  let R : ℝ := ‖e.toContinuousLinearMap‖ + ‖((1 : Fin m → ℂ), (0 : Fin m → ℂ))‖ + 1
  obtain ⟨q, hq, hhq⟩ := localized_word_root_sublevel
    (fun i => eraseCoefficients (w i)) hB F hF hF0 h hh δ R
    (by dsimp only [R]; have hn := norm_nonneg e.toContinuousLinearMap; linarith) h1 hi
    (fun q _ hq => by dsimp only [R]; have hn := hnorm q hq; have hp := norm_nonneg ((1 : Fin m → ℂ), (0 : Fin m → ℂ)); linarith)
    (fun q ht hq => by rw [hsizeroot q hq]; exact hiso q.1 ht _ (hroot q hq).2)
  refine ⟨fun i => normalizeQuaternion (e.symm q i), (hroot (1, q) hq).2, ?_⟩
  simpa only [hsizeroot (1, q) hq] using hhq
end EilenbergGanea


end

end OAI
