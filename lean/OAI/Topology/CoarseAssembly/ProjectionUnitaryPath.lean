import OAI.Topology.CoarseAssembly.FredholmModule
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

namespace OAI

/-! # An explicit unitary path for changing a projection's sign -/

noncomputable section

namespace CoarseAssembly.Analytic

def semicircleValue (t : Interval) : ℂ :=
  ⟨1 - 2 * t.val, 2 * Real.sqrt (t.val * (1 - t.val))⟩

theorem semicircleValue_star_mul (t : Interval) :
    star (semicircleValue t) * semicircleValue t = 1 := by
  have hsq := Real.sq_sqrt (mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2))
  apply Complex.ext
  · change (1 - 2 * t.val) * (1 - 2 * t.val) -
      (-(2 * Real.sqrt (t.val * (1 - t.val)))) *
        (2 * Real.sqrt (t.val * (1 - t.val))) = 1
    nlinarith
  · change (1 - 2 * t.val) * (2 * Real.sqrt (t.val * (1 - t.val))) +
      (-(2 * Real.sqrt (t.val * (1 - t.val)))) * (1 - 2 * t.val) = 0
    ring

def semicircleUnitary (t : Interval) : unitary ℂ :=
  ⟨semicircleValue t, semicircleValue_star_mul t, by
    rw [mul_comm]; exact semicircleValue_star_mul t⟩

attribute [local fun_prop] Continuous.const_mul continuous_mul_const in
theorem semicircleUnitary_continuous : Continuous semicircleUnitary := by
  apply Continuous.subtype_mk
  change Continuous (fun t : Interval => semicircleValue t)
  simp only [semicircleValue, Complex.mk_eq_add_mul_I]
  fun_prop

@[simp] theorem semicircleUnitary_start : semicircleUnitary start = 1 := by
  apply Subtype.ext
  change semicircleValue start = 1
  apply Complex.ext <;> norm_num [semicircleValue, start]

@[simp] theorem semicircleUnitary_finish : (semicircleUnitary finish : ℂ) = -1 := by
  apply Complex.ext <;> norm_num [semicircleUnitary, semicircleValue, finish]

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def projectionPhase (P : A) (hP : IsStarProjection P) (z : unitary ℂ) : unitary A := by
  let Q := 1 - P
  have hQQ : Q * Q = Q := hP.one_sub.isIdempotentElem
  have hPP : P * P = P := hP.isIdempotentElem
  have hPQ : P * Q = 0 := hP.mul_one_sub_self
  have hQP : Q * P = 0 := hP.one_sub_mul_self
  have hz : star (z : ℂ) * (z : ℂ) = 1 := Unitary.coe_star_mul_self z
  have hz' : (z : ℂ) * star (z : ℂ) = 1 := Unitary.coe_mul_star_self z
  refine ⟨Q + (z : ℂ) • P, ?_, ?_⟩
  · change star (Q + (z : ℂ) • P) * (Q + (z : ℂ) • P) = 1
    rw [star_add, star_smul, hP.isSelfAdjoint.star_eq,
      hP.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hQQ, mul_smul_comm, hQP, smul_zero, smul_mul_assoc, hPQ, smul_zero,
      smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
    rw [hz, one_smul, add_zero, zero_add]
    dsimp only [Q]
    abel
  · change (Q + (z : ℂ) • P) * star (Q + (z : ℂ) • P) = 1
    rw [star_add, star_smul, hP.isSelfAdjoint.star_eq,
      hP.one_sub.isSelfAdjoint.star_eq, add_mul, mul_add, mul_add,
      hQQ, mul_smul_comm, hQP, smul_zero, smul_mul_assoc, hPQ, smul_zero,
      smul_mul_assoc, mul_smul_comm, hPP, smul_smul]
    rw [hz', one_smul, add_zero, zero_add]
    dsimp only [Q]
    abel

def projectionSignPath (P : A) (hP : IsStarProjection P) (t : Interval) : unitary A :=
  projectionPhase P hP (semicircleUnitary t)

theorem projectionSignPath_continuous [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul ℂ A] (P : A) (hP : IsStarProjection P) :
    Continuous (projectionSignPath P hP) := by
  apply Continuous.subtype_mk
  exact continuous_const.add
    ((continuous_subtype_val.comp semicircleUnitary_continuous).smul continuous_const)

@[simp] theorem projectionSignPath_start (P : A) (hP : IsStarProjection P) :
    projectionSignPath P hP start = 1 := by
  apply Subtype.ext
  change 1 - P + (semicircleUnitary start : ℂ) • P = 1
  rw [semicircleUnitary_start]
  simp

@[simp] theorem projectionSignPath_finish (P : A) (hP : IsStarProjection P) :
    (projectionSignPath P hP finish : A) = 1 - (2 : ℂ) • P := by
  change 1 - P + (semicircleUnitary finish : ℂ) • P = _
  rw [semicircleUnitary_finish]
  module

end CoarseAssembly.Analytic

end

end OAI
