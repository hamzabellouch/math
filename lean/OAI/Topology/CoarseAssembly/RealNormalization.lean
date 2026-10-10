import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Scalar functions for involutive Fredholm normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

def inverseSqrtCorrection (t : ℝ) : ℝ := (Real.sqrt (t + 1))⁻¹ - 1

@[simp] theorem inverseSqrtCorrection_zero : inverseSqrtCorrection 0 = 0 := by
  simp [inverseSqrtCorrection]

theorem inverseSqrtCorrection_continuousAt {t : ℝ} (ht : 0 < t + 1) :
    ContinuousAt inverseSqrtCorrection t := by
  have hs : Real.sqrt (t + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  exact ((Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousAt.inv₀ hs).sub
    continuousAt_const

def normalizedReal (x : ℝ) : ℝ := x + x * inverseSqrtCorrection (x ^ 2 - 1)

theorem normalizedReal_eq (x : ℝ) : normalizedReal x = x * |x|⁻¹ := by
  simp only [normalizedReal, inverseSqrtCorrection, sub_add_cancel, Real.sqrt_sq_eq_abs]
  ring

theorem normalizedReal_sq {x : ℝ} (hx : x ≠ 0) : normalizedReal x ^ 2 = 1 := by
  rw [normalizedReal_eq, mul_pow, inv_pow, sq_abs]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hx)

end CoarseAssembly.Analytic

end

end OAI
