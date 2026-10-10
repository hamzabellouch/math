import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The actual congruence quotients and diagonal holonomies

The congruence quotient is `SL₃(ℤ/2^kℤ)`, including the singleton quotient
for `k = 0`.
Its diagonal matrices have entries `t,t⁻¹,1`, and the finite-level matrices
are obtained by the genuine 2-adic reduction maps.
-/

namespace CoarseAssembly.Congruence

theorem diagonal_one {R : Type*} [CommRing R] :
    diagonal (1 : Rˣ) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, Matrix.diagonal]

theorem diagonal_mul {R : Type*} [CommRing R] (s t : Rˣ) :
    diagonal (s * t) = diagonal s * diagonal t := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

/-- The diagonal assignment respects the unit-group multiplication. -/
def diagonalHom {R : Type*} [CommRing R] : Rˣ →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun := diagonal
  map_one' := diagonal_one
  map_mul' := diagonal_mul

/-- Powers of the diagonal holonomy have the expected Laurent trace. -/
theorem trace_diagonal_pow {R : Type*} [CommRing R] (t : Rˣ) (m : ℕ) :
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (t ^ m : Rˣ) + ((t ^ m)⁻¹ : Rˣ) + 1 := by
  change Matrix.trace ((diagonalHom t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R) = _
  rw [← map_pow]
  simp [diagonalHom, diagonal, Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

theorem trace_diagonal_zpow {R : Type*} [CommRing R] (t : Rˣ) (m : ℤ) :
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
      (t ^ m : Rˣ) + ((t ^ m)⁻¹ : Rˣ) + 1 := by
  change Matrix.trace ((diagonalHom t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R) = _
  rw [← map_zpow]
  simp [diagonalHom, diagonal, Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

/-- Reversing the signed charge leaves the diagonal trace unchanged. -/
theorem trace_diagonal_neg {R : Type*} [CommRing R] (t : Rˣ) (m : ℤ) :
    Matrix.trace ((diagonal t ^ (-m) : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) := by
  rw [trace_diagonal_zpow t (-m), trace_diagonal_zpow t m]
  simp only [zpow_neg, inv_inv]
  rw [add_comm (((t ^ m)⁻¹ : Rˣ) : R)]

theorem trace_conjugate {R : Type*} [CommRing R]
    (q z : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.trace ((z⁻¹ * q * z : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Matrix.trace (q : Matrix (Fin 3) (Fin 3) R) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

/-- Integral word traces reduce to their ordinary residue classes. -/
theorem trace_reduce (k : ℕ) (w : ArithmeticGroup) :
    Matrix.trace (reduce k w : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
      ((Matrix.trace (w : Matrix (Fin 3) (Fin 3) ℤ) : ℤ) : ZMod (2 ^ k)) := by
  simp [reduce, Matrix.trace, Matrix.SpecialLinearGroup.map_apply_coe]

end CoarseAssembly.Congruence

end OAI
