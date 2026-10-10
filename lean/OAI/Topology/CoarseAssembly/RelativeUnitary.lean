import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.NonUnitalK1
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Unitaries equal to one modulo a nonunital subalgebra

The scalar part is kept explicit, so no faithfulness assumption on a
unitization representation is needed to obtain its K₁ class.
-/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A : Type*} [CStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

theorem relativePart_mul_star (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    star (relativePart S u hu) + relativePart S u hu +
        relativePart S u hu * star (relativePart S u hu) = 0 := by
  apply Subtype.ext
  change star ((u : A) - 1) + ((u : A) - 1) +
    ((u : A) - 1) * star ((u : A) - 1) = 0
  rw [star_sub, star_one]
  have h := Unitary.coe_mul_star_self u
  change (u : A) * star (u : A) = 1 at h
  noncomm_ring [h]

theorem relativePart_star_mul (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    relativePart S u hu + star (relativePart S u hu) +
        star (relativePart S u hu) * relativePart S u hu = 0 := by
  apply Subtype.ext
  change ((u : A) - 1) + star ((u : A) - 1) +
    star ((u : A) - 1) * ((u : A) - 1) = 0
  rw [star_sub, star_one]
  have h := Unitary.coe_star_mul_self u
  change star (u : A) * (u : A) = 1 at h
  noncomm_ring [h]

@[simp] theorem relativeUnitary_val (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    (relativeUnitary S u hu : Unitization ℂ S) =
      1 + (relativePart S u hu : Unitization ℂ S) := rfl

@[simp] theorem relativeUnitary_scalar (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    (relativeUnitary S u hu : Unitization ℂ S).fst = 1 := by
  simp

theorem relativeMatrix_scalar (u : unitary A) (hu : (u : A) - 1 ∈ S) :
    TopologicalK1.mapGL (Unitization.fstHom ℂ S).toRingHom 1 (relativeMatrix S u hu) = 1 := by
  apply Units.ext
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  simp [TopologicalK1.mapGL, relativeMatrix, Matrix.scalar_apply,
    Unitary.val_toUnits_apply, hij]

variable [hS : IsClosed (S : Set A)]

theorem relativeClass_one (hu : ((1 : unitary A) : A) - 1 ∈ S) :
    relativeClass S 1 hu = 0 := by
  have hr : relativePart S 1 hu = 0 := by
    apply Subtype.ext
    simp [relativePart]
  have hm : relativeMatrix S 1 hu = 1 := by
    apply Units.ext
    change Matrix.scalar (Fin 1)
      (1 + (relativePart S 1 hu : Unitization ℂ S)) = 1
    rw [hr]
    simp
  apply Subtype.ext
  change TopologicalK1.matrixClass (Unitization ℂ S) (relativeMatrix S 1 hu) = 0
  rw [hm, TopologicalK1.matrixClass_one]

theorem relativeClass_eq_zero {u : unitary A} (hu : (u : A) - 1 ∈ S) (h : u = 1) :
    relativeClass S u hu = 0 := by
  subst u
  exact relativeClass_one S hu

end CoarseAssembly.OperatorKTheory

end

end OAI
