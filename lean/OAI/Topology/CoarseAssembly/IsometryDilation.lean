import OAI.Topology.CoarseAssembly.InvolutionUnitaryPath
import OAI.Topology.CoarseAssembly.K1TwoByTwo
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace OAI

/-! # The explicit two-by-two dilation of a spatial isometry -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

def isometryDilation (V : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1 - V * star V, V; star V, 0]

theorem isometryDilation_selfAdjoint (V : A) : IsSelfAdjoint (isometryDilation V) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [isometryDilation, Matrix.star_apply]

theorem isometry_complement_relations (V : A) (hV : star V * V = 1) :
    (1 - V * star V) * (1 - V * star V) = 1 - V * star V ∧
      (1 - V * star V) * V = 0 ∧ star V * (1 - V * star V) = 0 := by
  have hP : V * star V * (V * star V) = V * star V := by
    calc
      _ = V * (star V * V) * star V := by noncomm_ring
      _ = _ := by rw [hV, mul_one]
  have hPV : V * star V * V = V := by rw [mul_assoc, hV, mul_one]
  have hVP : star V * (V * star V) = star V := by rw [← mul_assoc, hV, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · rw [sub_mul, one_mul, hPV, sub_self]
  · rw [mul_sub, mul_one, hVP, sub_self]

theorem isometryDilation_sq (V : A) (hV : star V * V = 1) :
    isometryDilation V * isometryDilation V = 1 := by
  obtain ⟨hQQ, hQV, hVQ⟩ := isometry_complement_relations V hV
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change (1 - V * star V) * (1 - V * star V) + V * star V = 1
    rw [hQQ]
    abel
  · change (1 - V * star V) * V + V * 0 = 0
    rw [hQV, mul_zero, add_zero]
  · change star V * (1 - V * star V) + 0 * star V = 0
    rw [hVQ, zero_mul, add_zero]
  · change star V * V + 0 * 0 = 1
    rw [hV, zero_mul, add_zero]

def isometryDilationPath (V : A) (hV : star V * V = 1) :
    Interval → unitary (Matrix (Fin 2) (Fin 2) A) :=
  involutionUnitaryPath (isometryDilation V) (isometryDilation_selfAdjoint V)
    (isometryDilation_sq V hV)

theorem isometryDilationPath_continuous (V : A) (hV : star V * V = 1) :
    Continuous (isometryDilationPath V hV) := involutionUnitaryPath_continuous _ _ _

@[simp] theorem isometryDilationPath_start (V : A) (hV : star V * V = 1) :
    isometryDilationPath V hV start = 1 := involutionUnitaryPath_start _ _ _

@[simp] theorem isometryDilationPath_finish (V : A) (hV : star V * V = 1) :
    (isometryDilationPath V hV finish).val = isometryDilation V :=
  involutionUnitaryPath_finish _ _ _

/-- Conjugating the stabilized operator gives its identity extension. -/
theorem isometryDilation_conjugation (V a : A) (hV : star V * V = 1) :
    isometryDilation V * !![1, 0; 0, a] * isometryDilation V =
      !![1 + V * (a - 1) * star V, 0; 0, 1] := by
  obtain ⟨hQQ, hQV, hVQ⟩ := isometry_complement_relations V hV
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change ((1 - V * star V) * 1 + V * 0) * (1 - V * star V) +
      ((1 - V * star V) * 0 + V * a) * star V = 1 + V * (a - 1) * star V
    simp only [mul_one, mul_zero, add_zero, zero_add]
    rw [hQQ]
    noncomm_ring
  · change ((1 - V * star V) * 1 + V * 0) * V +
      ((1 - V * star V) * 0 + V * a) * 0 = 0
    simp only [mul_one, mul_zero, add_zero]
    exact hQV
  · change (star V * 1 + 0 * 0) * (1 - V * star V) +
      (star V * 0 + 0 * a) * star V = 0
    simp only [mul_one, mul_zero, zero_mul, add_zero]
    exact hVQ
  · change (star V * 1 + 0 * 0) * V + (star V * 0 + 0 * a) * 0 = 1
    simp only [mul_one, mul_zero, zero_mul, add_zero]
    exact hV

end CoarseAssembly.Analytic

end

end OAI
