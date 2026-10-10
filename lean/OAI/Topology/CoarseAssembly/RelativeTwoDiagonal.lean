import OAI.Topology.CoarseAssembly.RelativeTwoHomotopy

namespace OAI

/-! # Diagonal relative matrices and addition in Roe K₁ -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {R : Type*} [CStarAlgebra R]

def diagonalTwoUnitary (u v : unitary R) : unitary (Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨Matrix.diagonal (fun i => if i = 0 then (u : R) else (v : R)), ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal]

variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

omit hS in
theorem diagonalTwoUnitary_relative (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    ∀ i j, ((diagonalTwoUnitary u v : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [diagonalTwoUnitary, Matrix.diagonal] using hu
  · simp [diagonalTwoUnitary, Matrix.diagonal]
  · simp [diagonalTwoUnitary, Matrix.diagonal]
  · simpa [diagonalTwoUnitary, Matrix.diagonal] using hv

theorem relativeTwoMatrix_diagonal (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    relativeTwoMatrix S (diagonalTwoUnitary u v) (diagonalTwoUnitary_relative S u v hu hv) =
      TopologicalK1.diagonalTwoUnits (Unitary.toUnits (relativeUnitary S u hu))
        (Unitary.toUnits (relativeUnitary S v hv)) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom, relativeTwoPart,
      diagonalTwoUnitary, TopologicalK1.diagonalTwoUnits, Matrix.diagonal,
      relativeUnitary, relativePart]
  all_goals
    change ((0 : S) : Unitization ℂ S) = 0
    simp

/-- Two diagonal relative unitaries represent the sum of their K₁ classes. -/
theorem relativeTwoClass_diagonal (u v : unitary R)
    (hu : (u : R) - 1 ∈ S) (hv : (v : R) - 1 ∈ S) :
    relativeTwoClass S (diagonalTwoUnitary u v) (diagonalTwoUnitary_relative S u v hu hv) =
      relativeClass S u hu + relativeClass S v hv := by
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S)
      (relativeTwoMatrix S (diagonalTwoUnitary u v) _) = _
  rw [relativeTwoMatrix_diagonal, TopologicalK1.diagonalTwo_matrixClass]
  rfl

end CoarseAssembly.OperatorKTheory

end

end OAI
