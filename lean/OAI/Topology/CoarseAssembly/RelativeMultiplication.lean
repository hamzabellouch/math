import OAI.Topology.CoarseAssembly.RelativeUnitary

namespace OAI

/-! # Multiplication of relative unitaries adds their actual K₁ classes -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

theorem relative_mul_mem (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    ((u * v : unitary A) : A) - 1 ∈ S := by
  have he : (u : A) * (v : A) - 1 =
      ((u : A) - 1) + ((v : A) - 1) + ((u : A) - 1) * ((v : A) - 1) := by
    noncomm_ring
  change (u : A) * (v : A) - 1 ∈ S
  rw [he]
  exact S.add_mem (S.add_mem hu hv) (S.mul_mem hu hv)

theorem relativePart_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativePart S (u * v) (relative_mul_mem S u v hu hv) =
      relativePart S u hu + relativePart S v hv + relativePart S u hu * relativePart S v hv := by
  apply Subtype.ext
  change (u : A) * (v : A) - 1 = _
  change (u : A) * (v : A) - 1 =
    ((u : A) - 1) + ((v : A) - 1) + ((u : A) - 1) * ((v : A) - 1)
  noncomm_ring

theorem relativeUnitary_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativeUnitary S (u * v) (relative_mul_mem S u v hu hv) =
      relativeUnitary S u hu * relativeUnitary S v hv := by
  apply Subtype.ext
  change 1 + (relativePart S (u * v) (relative_mul_mem S u v hu hv) : Unitization ℂ S) =
    (1 + (relativePart S u hu : Unitization ℂ S)) *
      (1 + (relativePart S v hv : Unitization ℂ S))
  rw [relativePart_mul S u v hu hv, Unitization.inr_add, Unitization.inr_add, Unitization.inr_mul]
  noncomm_ring

variable [hS : IsClosed (S : Set A)]

theorem relativeClass_mul (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    relativeClass S (u * v) (relative_mul_mem S u v hu hv) =
      relativeClass S u hu + relativeClass S v hv := by
  have hm : relativeMatrix S (u * v) (relative_mul_mem S u v hu hv) =
      relativeMatrix S u hu * relativeMatrix S v hv := by
    unfold relativeMatrix
    rw [relativeUnitary_mul, map_mul, map_mul]
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S)
    (relativeMatrix S (u * v) _) = _
  rw [hm, TopologicalK1.matrixClass_mul]
  rfl

end CoarseAssembly.OperatorKTheory

end

end OAI
