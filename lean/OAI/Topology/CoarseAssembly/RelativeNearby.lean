import OAI.Topology.CoarseAssembly.K1Nearby
import OAI.Topology.CoarseAssembly.RelativeUnitary

namespace OAI

/-! # Nearby relative unitaries have the same actual Roe K₁ class -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A]
  (S : NonUnitalStarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

theorem relativeUnitary_sub_norm (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S) :
    ‖(relativeUnitary S v hv : Unitization ℂ S) - relativeUnitary S u hu‖ = ‖(v : A) - u‖ := by
  have he : (relativeUnitary S v hv : Unitization ℂ S) - relativeUnitary S u hu =
      ((relativePart S v hv - relativePart S u hu : S) : Unitization ℂ S) := by
    rw [Unitization.inr_sub, relativeUnitary_val, relativeUnitary_val]
    abel
  rw [he, Unitization.norm_inr]
  change ‖((v : A) - 1) - ((u : A) - 1)‖ = ‖(v : A) - u‖
  congr 1
  abel

theorem relativeClass_eq_of_nearby (u v : unitary A)
    (hu : (u : A) - 1 ∈ S) (hv : (v : A) - 1 ∈ S)
    (h : ‖(v : A) - u‖ < 1) : relativeClass S u hu = relativeClass S v hv := by
  let u' := relativeUnitary S u hu
  let v' := relativeUnitary S v hv
  have hn : ‖(v' : Unitization ℂ S) - u'‖ < 1 := by
    rw [relativeUnitary_sub_norm]
    exact h
  have hi : ‖(↑(Unitary.toUnits u')⁻¹ : Unitization ℂ S)‖ = 1 := by
    change ‖star (u' : Unitization ℂ S)‖ = 1
    rw [norm_star]
    exact CStarRing.norm_coe_unitary u'
  apply Subtype.ext
  apply TopologicalK1.matrixClass_scalar_eq_of_nearby (Unitary.toUnits u') (Unitary.toUnits v')
  simpa only [hi, inv_one, Unitary.val_toUnits_apply] using hn

end CoarseAssembly.OperatorKTheory

end

end OAI
