import OAI.Topology.CoarseAssembly.RelativeUnitary

namespace OAI

/-! # Naturality of the relative-unitary K₁ representative -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (S : NonUnitalStarSubalgebra ℂ A) (T : NonUnitalStarSubalgebra ℂ B)
  [hS : IsClosed (S : Set A)] [hT : IsClosed (T : Set B)]

theorem map_relativeClass (φ : S →⋆ₙₐ[ℂ] T)
    (u : unitary A) (v : unitary B) (hu : (u : A) - 1 ∈ S) (hv : (v : B) - 1 ∈ T)
    (h : φ (relativePart S u hu) = relativePart T v hv) :
    map φ (relativeClass S u hu) = relativeClass T v hv := by
  apply Subtype.ext
  change unitizationMap φ (TopologicalK1.matrixClass (Unitization ℂ S)
    (relativeMatrix S u hu)) =
      TopologicalK1.matrixClass (Unitization ℂ T) (relativeMatrix T v hv)
  rw [unitizationMap_matrixClass]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap φ
      (Matrix.scalar (Fin 1) (1 + (relativePart S u hu : Unitization ℂ S)) i j) =
    Matrix.scalar (Fin 1) (1 + (relativePart T v hv : Unitization ℂ T)) i j
  have hij : i = j := Subsingleton.elim _ _
  simp only [Matrix.scalar_apply, hij, Matrix.diagonal_apply_eq]
  rw [map_add, map_one, Unitization.starMap_inr, h]

end CoarseAssembly.OperatorKTheory

end

end OAI
