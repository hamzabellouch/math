import OAI.Topology.CoarseAssembly.TopologicalK1
import Mathlib.Tactic.FinCases

namespace OAI

/-! # The two-by-two stabilization used for spatial K₁ representatives -/

noncomputable section

namespace CoarseAssembly.TopologicalK1

variable {R : Type*} [Ring R] [TopologicalSpace R]

theorem matrixClass_inv {n : ℕ} (g : InvertibleMatrix R n) :
    matrixClass R g⁻¹ = -matrixClass R g := by
  have h := matrixClass_mul g g⁻¹
  rw [mul_inv_cancel, matrixClass_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

theorem matrixClass_conjugate {n : ℕ} (g h : InvertibleMatrix R n) :
    matrixClass R (g * h * g⁻¹) = matrixClass R h := by
  rw [matrixClass_mul, matrixClass_mul, matrixClass_inv]
  abel

def scalarUnitMatrix (g : Rˣ) : InvertibleMatrix R 1 :=
  Units.map (Matrix.scalar (Fin 1)).toMonoidHom g

def diagonalTwoUnits (g h : Rˣ) : InvertibleMatrix R 2 :=
  Units.map (Matrix.diagonalRingHom (Fin 2) R).toMonoidHom
    { val := fun i => if i = 0 then (g : R) else (h : R)
      inv := fun i => if i = 0 then (g⁻¹ : Rˣ) else (h⁻¹ : Rˣ)
      val_inv := by ext i; by_cases hi : i = 0 <;> simp [hi]
      inv_val := by ext i; by_cases hi : i = 0 <;> simp [hi] }

omit [TopologicalSpace R] in
theorem diagonalTwo_stabilizes (g : Rˣ) :
    IsStabilization R (scalarUnitMatrix g) (diagonalTwoUnits g 1) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [IsStabilization, diagonalTwoUnits, scalarUnitMatrix, Matrix.diagonal,
      Matrix.scalar, Matrix.fromBlocks, Matrix.submatrix, finSumFinEquiv]

theorem diagonalTwo_matrixClass_one (g : Rˣ) :
    matrixClass R (diagonalTwoUnits g 1) = matrixClass R (scalarUnitMatrix g) :=
  (matrixClass_stabilize _ _ (diagonalTwo_stabilizes g)).symm

def flipTwoUnits : InvertibleMatrix R 2 where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [TopologicalSpace R] in
theorem diagonalTwo_flip (g h : Rˣ) :
    flipTwoUnits * diagonalTwoUnits g h * (flipTwoUnits : InvertibleMatrix R 2)⁻¹ =
      diagonalTwoUnits h g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [flipTwoUnits, diagonalTwoUnits, Matrix.mul_apply, Matrix.diagonal,
      Matrix.vecHead, Matrix.vecTail]

theorem diagonalTwo_matrixClass_swap (g h : Rˣ) :
    matrixClass R (diagonalTwoUnits g h) = matrixClass R (diagonalTwoUnits h g) := by
  exact (matrixClass_conjugate (flipTwoUnits : InvertibleMatrix R 2)
    (diagonalTwoUnits g h)).symm.trans (congrArg (matrixClass R) (diagonalTwo_flip g h))

omit [TopologicalSpace R] in
theorem diagonalTwo_mul (g h : Rˣ) :
    diagonalTwoUnits g h = diagonalTwoUnits g 1 * diagonalTwoUnits 1 h := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalTwoUnits, Matrix.mul_apply, Matrix.diagonal]

/-- The exact stabilization identity for two relative unitaries. -/
theorem diagonalTwo_matrixClass (g h : Rˣ) :
    matrixClass R (diagonalTwoUnits g h) =
      matrixClass R (scalarUnitMatrix g) + matrixClass R (scalarUnitMatrix h) := by
  rw [diagonalTwo_mul, matrixClass_mul, diagonalTwo_matrixClass_one,
    diagonalTwo_matrixClass_swap 1 h, diagonalTwo_matrixClass_one]

end CoarseAssembly.TopologicalK1

end

end OAI
