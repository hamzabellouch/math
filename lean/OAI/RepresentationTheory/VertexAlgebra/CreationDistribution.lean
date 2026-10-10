import OAI.RepresentationTheory.VertexAlgebra.CreationBoundaryUniqueness
import OAI.RepresentationTheory.VertexAlgebra.Foundations

namespace OAI

noncomputable section
namespace StronglyRationalVOA
open CreationBoundary

def ScalarCreationSmear (b : ℕ → ℂ) (f : SmoothCircleFunction) : ℂ :=
  ∑' n : ℕ, f.coefficient (-(n:ℤ))*b n

theorem summable_twiceWeighted_creation {b : ℕ → ℂ} {C : ℝ} {p : ℕ}
    (hb : ∀ n, ‖b n‖ ≤ C*(1+(n:ℝ))^p) (f : SmoothCircleFunction) :
    Summable (weightTwo (fun n => f.coefficient (-(n:ℤ))*b n)) := by
  have hs := (summable_int_iff_summable_nat_and_neg.mp (f.rapid_coefficients (p+2))).2
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] at hs
  apply Summable.of_nonneg_of_le (fun n => by unfold weightTwo; positivity) _ (hs.mul_right C)
  intro n
  unfold weightTwo
  rw [norm_mul]
  calc
    _ ≤ ‖f.coefficient (-(n:ℤ))‖*(C*(1+(n:ℝ))^p)*(1+(n:ℝ))^2 := by gcongr; exact hb n
    _ = _ := by rw [pow_add]; ring

theorem translate_creationSmear (b : ℕ → ℂ) (f : SmoothCircleFunction) (t : ℝ) :
    ScalarCreationSmear b (f.translate t) =
      powerSum (fun n => f.coefficient (-(n:ℤ))*b n) (circlePoint t) := by
  apply tsum_congr
  intro n
  rw [SmoothCircleFunction.translate_coefficient]
  have he : Complex.exp (-((t*((-(n:ℤ)):ℝ):ℝ)*Complex.I)) = circlePoint t ^ n := by
    rw [circlePoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [Int.cast_neg]
  rw [he]
  ring

namespace SmoothCircleFunction
local instance creationDistributionPeriodPositive : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

theorem exists_coefficient_ne_zero {f : SmoothCircleFunction}
    {x : AddCircle (2*Real.pi)} (hx : f.onCircle x ≠ 0) :
    ∃ n : ℤ, f.coefficient n ≠ 0 := by
  by_contra h
  push Not at h
  have hs : Summable (fourierCoeff f.toContinuousMap) := by
    change Summable (fun n => fourierCoeff f.toContinuousMap n)
    simp_rw [f.fourierCoeff_toContinuousMap]
    exact (by simpa using f.rapid_coefficients 0 : Summable (fun n => ‖f.coefficient n‖)).of_norm
  have H := has_pointwise_sum_fourier_series_of_summable hs x
  have hfun : (fun n => fourierCoeff f.toContinuousMap n • fourier n x) = (fun _ : ℤ => (0:ℂ)) := by
    funext n
    rw [f.fourierCoeff_toContinuousMap, h]
    simp
  rw [hfun] at H
  exact hx ((HasSum.tsum_eq H).symm.trans (by simp))

theorem exists_arc_test_zeroCoefficient (I : ProperCircleArc) :
    ∃ f : SmoothCircleFunction, tsupport f.onCircle ⊆ I.carrier ∧ f.coefficient 0 ≠ 0 := by
  have hx : (((I.left+I.right)/2:ℝ):AddCircle (2*Real.pi)) ∈ I.carrier := by
    exact ⟨(I.left+I.right)/2, ⟨by linarith [I.nonempty'], by linarith [I.nonempty']⟩, rfl⟩
  obtain ⟨χ, _, hχ1, hχI⟩ := exists_real_cutoff isCompact_singleton I.isOpen_carrier
    (Set.singleton_subset_iff.mpr hx)
  have hχx := hχ1 (Set.mem_singleton _)
  change χ.onCircle _ = 1 at hχx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, χ.coefficient n ≠ 0 :=
    exists_coefficient_ne_zero (by rw [hχx]; exact one_ne_zero)
  refine ⟨χ.modulate (-n), (χ.modulate_support (-n)).trans hχI, ?_⟩
  simpa [modulate_coefficient] using hn
end SmoothCircleFunction

theorem scalarCreation_constant_zero_of_local {b : ℕ → ℂ} {C : ℝ} {p : ℕ}
    (hb : ∀ n, ‖b n‖ ≤ C*(1+(n:ℝ))^p) (I : ProperCircleArc)
    (hzero : ∀ f : SmoothCircleFunction, tsupport f.onCircle ⊆ I.carrier →
      ScalarCreationSmear b f = 0) : b 0 = 0 := by
  obtain ⟨f, hf, hf0⟩ := SmoothCircleFunction.exists_arc_test_zeroCoefficient I
  obtain ⟨ε, hε, hfε⟩ := f.exists_translation_radius I.isOpen_carrier hf
  have hz : ∀ t : ℝ, |t| < ε →
      powerSum (fun n => f.coefficient (-(n:ℤ))*b n) (circlePoint t) = 0 := by
    intro t ht
    rw [← translate_creationSmear]
    exact hzero _ (hfε t ht)
  have H := constant_zero_of_boundary (summable_twiceWeighted_creation hb f) hε hz
  simp only [Nat.cast_zero, neg_zero] at H
  exact (mul_eq_zero.mp H).resolve_left hf0

end StronglyRationalVOA

end

end OAI
