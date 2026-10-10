import OAI.Topology.CoarseAssembly.IsometryDilation

namespace OAI

/-! # Swapping two isometric images by a partial-isometry dilation -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

def partialIsometryDilation (T : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1 - star T * T, star T; T, 1 - T * star T]

theorem partialIsometryDilation_selfAdjoint (T : A) :
    IsSelfAdjoint (partialIsometryDilation T) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [partialIsometryDilation, Matrix.star_apply]

theorem partialIsometry_star_relation (T : A) (hT : T * star T * T = T) :
    star T * T * star T = star T := by
  have h := congrArg star hT
  simpa only [star_mul, star_star, mul_assoc] using h

theorem partialIsometry_complement_relations (T : A) (hT : T * star T * T = T) :
    (1 - star T * T) * (1 - star T * T) = 1 - star T * T ∧
    (1 - T * star T) * (1 - T * star T) = 1 - T * star T ∧
    (1 - star T * T) * star T = 0 ∧ star T * (1 - T * star T) = 0 ∧
    T * (1 - star T * T) = 0 ∧ (1 - T * star T) * T = 0 := by
  have hs := partialIsometry_star_relation T hT
  have hP : (star T * T) * (star T * T) = star T * T := by
    calc
      _ = (star T * T * star T) * T := by noncomm_ring
      _ = _ := by rw [hs]
  have hQ : (T * star T) * (T * star T) = T * star T := by
    calc
      _ = (T * star T * T) * star T := by noncomm_ring
      _ = _ := by rw [hT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · noncomm_ring [hQ]
  · rw [sub_mul, one_mul, hs, sub_self]
  · rw [mul_sub, mul_one, ← mul_assoc, hs, sub_self]
  · rw [mul_sub, mul_one, ← mul_assoc, hT, sub_self]
  · rw [sub_mul, one_mul, hT, sub_self]

theorem partialIsometryDilation_sq (T : A) (hT : T * star T * T = T) :
    partialIsometryDilation T * partialIsometryDilation T = 1 := by
  obtain ⟨hE, hF, hEs, hsF, hTE, hFT⟩ := partialIsometry_complement_relations T hT
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change (1 - star T * T) * (1 - star T * T) + star T * T = 1
    rw [hE]
    abel
  · change (1 - star T * T) * star T + star T * (1 - T * star T) = 0
    rw [hEs, hsF, add_zero]
  · change T * (1 - star T * T) + (1 - T * star T) * T = 0
    rw [hTE, hFT, add_zero]
  · change T * star T + (1 - T * star T) * (1 - T * star T) = 1
    rw [hF]
    abel

/-- A continuous path from one to the symmetry exchanging the two images. -/
def partialIsometryDilationPath (T : A) (hT : T * star T * T = T) :
    Interval → unitary (Matrix (Fin 2) (Fin 2) A) :=
  involutionUnitaryPath (partialIsometryDilation T) (partialIsometryDilation_selfAdjoint T)
    (partialIsometryDilation_sq T hT)

theorem partialIsometryDilationPath_continuous (T : A) (hT : T * star T * T = T) :
    Continuous (partialIsometryDilationPath T hT) := involutionUnitaryPath_continuous _ _ _

@[simp] theorem partialIsometryDilationPath_start (T : A) (hT : T * star T * T = T) :
    partialIsometryDilationPath T hT start = 1 := involutionUnitaryPath_start _ _ _

@[simp] theorem partialIsometryDilationPath_finish (T : A) (hT : T * star T * T = T) :
    (partialIsometryDilationPath T hT finish).val = partialIsometryDilation T :=
  involutionUnitaryPath_finish _ _ _

theorem partialIsometryDilation_conjugation (T f : A) (hT : T * star T * T = T)
    (hleft : (star T * T) * f = f) (hright : f * (star T * T) = f) :
    partialIsometryDilation T * !![1 + f, 0; 0, 1] * partialIsometryDilation T =
      !![1, 0; 0, 1 + T * f * star T] := by
  obtain ⟨hE, hF, hEs, hsF, hTE, hFT⟩ := partialIsometry_complement_relations T hT
  have hEf : (1 - star T * T) * f = 0 := by rw [sub_mul, one_mul, hleft, sub_self]
  have hfE : f * (1 - star T * T) = 0 := by rw [mul_sub, mul_one, hright, sub_self]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change ((1 - star T * T) * (1 + f) + star T * 0) * (1 - star T * T) +
      ((1 - star T * T) * 0 + star T * 1) * T = 1
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, hEf]
    rw [hE]
    abel
  · change ((1 - star T * T) * (1 + f) + star T * 0) * star T +
      ((1 - star T * T) * 0 + star T * 1) * (1 - T * star T) = 0
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, hEf, hEs, hsF]
  · change (T * (1 + f) + (1 - T * star T) * 0) * (1 - star T * T) +
      (T * 0 + (1 - T * star T) * 1) * T = 0
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, add_mul, mul_assoc, hfE, hTE, hFT]
  · change (T * (1 + f) + (1 - T * star T) * 0) * star T +
      (T * 0 + (1 - T * star T) * 1) * (1 - T * star T) = 1 + T * f * star T
    simp only [mul_add, mul_one, mul_zero, add_zero, zero_add, add_mul, hF]
    noncomm_ring

end CoarseAssembly.Analytic

end

end OAI
