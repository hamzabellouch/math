import OAI.Topology.CoarseAssembly.FiniteFiberMaps
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import OAI.Topology.CoarseAssembly.CongruenceMaps

namespace OAI

/-! # The actual finite-quotient averaging operators

Normalized left translations and their lazy average act on the spatial
fiber Hilbert spaces. They are contractions fixing the constant subspace.
The strict norm bound off constants is kept as the precise published
Kazhdan-gap input, rather than assuming any Roe transfer conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (Q : Type*) [Fintype Q] [Nonempty Q]

def constantProjection : lp (fun _ : Q => H) 2 →L[ℂ] lp (fun _ : Q => H) 2 :=
  (fiberConstantIsometry Q).toContinuousLinearMap.comp
    (fiberConstantIsometry Q).toContinuousLinearMap.adjoint

theorem constantProjection_idempotent :
    constantProjection (H := H) Q * constantProjection Q = constantProjection Q := by
  ext x
  simp [constantProjection]

theorem constantProjection_norm_le : ‖constantProjection (H := H) Q‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  have h := (fiberConstantIsometry (H := H) Q).norm_toContinuousLinearMap_le
  nlinarith [norm_nonneg (fiberConstantIsometry (H := H) Q).toContinuousLinearMap]

variable [Group Q]

def leftTranslation (g : Q) : lp (fun _ : Q => H) 2 ≃ₗᵢ[ℂ] lp (fun _ : Q => H) 2 :=
  reindexFiber (Equiv.mulLeft g)

omit [CompleteSpace H] [Nonempty Q] in
theorem leftTranslation_constant (g : Q) (h : H) :
    leftTranslation Q g (fiberConstant Q h) = fiberConstant Q h :=
  reindexFiber_constant _ _

theorem leftTranslation_projection (g : Q) :
    (leftTranslation (H := H) Q g).toLinearIsometry.toContinuousLinearMap *
      constantProjection Q = constantProjection Q := by
  apply ContinuousLinearMap.ext
  intro x
  change leftTranslation (H := H) Q g (fiberConstant (H := H) Q _) =
    fiberConstant (H := H) Q _
  exact leftTranslation_constant (H := H) Q g _

theorem projection_leftTranslation (g : Q) :
    constantProjection (H := H) Q *
      (leftTranslation Q g).toLinearIsometry.toContinuousLinearMap = constantProjection Q := by
  have he : (leftTranslation (H := H) Q g).toLinearIsometry.toContinuousLinearMap.adjoint =
      (leftTranslation Q g⁻¹).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hi := (leftTranslation (H := H) Q g).inner_map_map
      ((leftTranslation Q g⁻¹) x) y
    have hx : leftTranslation Q g (leftTranslation Q g⁻¹ x) = x := by
      apply lp.ext
      funext q
      simp [leftTranslation, reindexFiber_apply]
    rw [hx] at hi
    exact hi
  have hs := congrArg star (leftTranslation_projection (H := H) Q g⁻¹)
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint, constantProjection,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, ← he] using hs

variable (S : Finset ArithmeticGroup)

def meanTranslation (k : ℕ) :
    lp (fun _ : Quotient k => H) 2 →L[ℂ] lp (fun _ : Quotient k => H) 2 :=
  ((S.card : ℂ)⁻¹) • ∑ s ∈ S, (leftTranslation (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap

def lazyAverage (k : ℕ) :
    lp (fun _ : Quotient k => H) 2 →L[ℂ] lp (fun _ : Quotient k => H) 2 :=
  (1 / 2 : ℂ) • (1 + meanTranslation S k)

theorem meanTranslation_norm_le (k : ℕ) : ‖meanTranslation (H := H) S k‖ ≤ 1 := by
  have hsum : ‖∑ s ∈ S,
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap‖ ≤
      (S.card : ℝ) := by
    apply (norm_sum_le S (fun s =>
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap)).trans
    calc
      _ ≤ ∑ _s ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun s _ =>
        (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.norm_toContinuousLinearMap_le)
      _ = _ := by simp
  by_cases hS : S.card = 0
  · change ‖(((S.card : ℂ)⁻¹) • _)‖ ≤ (1 : ℝ)
    simp only [hS, Nat.cast_zero, inv_zero, zero_smul, norm_zero]
    exact (zero_le_one : (0 : ℝ) ≤ 1)
  · have hpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
    change ‖((S.card : ℂ)⁻¹) • (∑ s ∈ S,
      (leftTranslation (H := H) (Quotient k) (reduce k s)).toLinearIsometry.toContinuousLinearMap)‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)).trans_eq
      (inv_mul_cancel₀ (ne_of_gt hpos))

theorem lazyAverage_norm_le (k : ℕ) : ‖lazyAverage (H := H) S k‖ ≤ 1 := by
  have h := norm_add_le (1 : lp (fun _ : Quotient k => H) 2 →L[ℂ] _) (meanTranslation (H := H) S k)
  have hi : ‖(1 : lp (fun _ : Quotient k => H) 2 →L[ℂ] _)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hm := meanTranslation_norm_le (H := H) S k
  change ‖(1 / 2 : ℂ) • (1 + meanTranslation (H := H) S k)‖ ≤ 1
  rw [norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  linarith

theorem lazyAverage_projection (hS : S.Nonempty) (k : ℕ) :
    lazyAverage (H := H) S k * constantProjection (H := H) (Quotient k) =
      constantProjection (H := H) (Quotient k) := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : meanTranslation (H := H) S k * constantProjection (H := H) (Quotient k) =
      constantProjection (H := H) (Quotient k) := by
    simp only [meanTranslation, smul_mul_assoc, Finset.sum_mul, leftTranslation_projection,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [lazyAverage, smul_mul_assoc, add_mul, one_mul, hm]
  rw [← two_smul ℂ, smul_smul]
  norm_num

theorem projection_lazyAverage (hS : S.Nonempty) (k : ℕ) :
    constantProjection (H := H) (Quotient k) * lazyAverage S k =
      constantProjection (Quotient k) := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : constantProjection (H := H) (Quotient k) * meanTranslation S k =
      constantProjection (Quotient k) := by
    simp only [meanTranslation, mul_smul_comm, Finset.mul_sum, projection_leftTranslation,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [lazyAverage, mul_smul_comm, mul_add, mul_one, hm]
  rw [← two_smul ℂ, smul_smul]
  norm_num

end CoarseAssembly

end

end OAI
