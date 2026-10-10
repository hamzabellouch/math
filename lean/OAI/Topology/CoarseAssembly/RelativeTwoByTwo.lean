import OAI.Topology.CoarseAssembly.RelativeUnitary
import OAI.Topology.CoarseAssembly.K1TwoByTwo
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace OAI

/-! # Two-by-two relative unitaries for the spatial stabilization argument -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def matrixTwoStarHom (φ : A →⋆ₙₐ[ℂ] B) :
    Matrix (Fin 2) (Fin 2) A →⋆ₙₐ[ℂ] Matrix (Fin 2) (Fin 2) B where
  toFun T := T.map φ
  map_zero' := by ext i j; exact map_zero φ
  map_add' T U := by ext i j; exact map_add φ _ _
  map_mul' T U := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  map_smul' z T := by ext i j; exact map_smul φ z _
  map_star' T := by ext i j; exact map_star φ _

theorem matrixTwoStarHom_injective (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    Function.Injective (matrixTwoStarHom φ) := by
  intro T U h
  ext i j
  apply hφ
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M i j) h

theorem matrixTwoStarHom_continuous (φ : A →⋆ₙₐ[ℂ] B) (hφ : Continuous φ) :
    Continuous (matrixTwoStarHom φ) := by
  exact continuous_pi (fun i => continuous_pi (fun j =>
    hφ.comp ((continuous_apply j).comp (continuous_apply i))))

section Relative

variable {R : Type*} [CStarAlgebra R] (S : NonUnitalStarSubalgebra ℂ R)

def relativeTwoPart (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    Matrix (Fin 2) (Fin 2) S :=
  fun i j => ⟨((u : Matrix (Fin 2) (Fin 2) R) - 1) i j, hu i j⟩

variable [hS : IsClosed (S : Set R)]

theorem relativeTwoPart_coe (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    matrixTwoStarHom (NonUnitalStarSubalgebraClass.subtype S) (relativeTwoPart S u hu) =
      (u : Matrix (Fin 2) (Fin 2) R) - 1 := rfl

theorem relativeTwoPart_star_mul (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    relativeTwoPart S u hu + star (relativeTwoPart S u hu) +
      star (relativeTwoPart S u hu) * relativeTwoPart S u hu = 0 := by
  apply matrixTwoStarHom_injective (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective
  simp only [map_add, map_mul, map_star, map_zero, relativeTwoPart_coe]
  rw [star_sub, star_one]
  have h := Unitary.coe_star_mul_self u
  change star (u : Matrix (Fin 2) (Fin 2) R) * (u : Matrix (Fin 2) (Fin 2) R) = 1 at h
  noncomm_ring [h]

theorem relativeTwoPart_mul_star (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    star (relativeTwoPart S u hu) + relativeTwoPart S u hu +
      relativeTwoPart S u hu * star (relativeTwoPart S u hu) = 0 := by
  apply matrixTwoStarHom_injective (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective
  simp only [map_add, map_mul, map_star, map_zero, relativeTwoPart_coe]
  rw [star_sub, star_one]
  have h := Unitary.coe_mul_star_self u
  change (u : Matrix (Fin 2) (Fin 2) R) * star (u : Matrix (Fin 2) (Fin 2) R) = 1 at h
  noncomm_ring [h]

def relativeTwoUnitary (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    unitary (Matrix (Fin 2) (Fin 2) (Unitization ℂ S)) := by
  let φ := matrixTwoStarHom (Unitization.inrNonUnitalStarAlgHom ℂ S)
  let P := relativeTwoPart S u hu
  refine ⟨1 + φ P, ?_, ?_⟩
  · change star (1 + φ P) * (1 + φ P) = 1
    calc
      _ = 1 + (φ P + star (φ P) + star (φ P) * φ P) := by
        rw [star_add, star_one]
        noncomm_ring
      _ = 1 + φ (P + star P + star P * P) := by rw [map_add, map_add, map_mul, map_star]
      _ = 1 := by rw [relativeTwoPart_star_mul, map_zero, add_zero]
  · change (1 + φ P) * star (1 + φ P) = 1
    calc
      _ = 1 + (star (φ P) + φ P + φ P * star (φ P)) := by
        rw [star_add, star_one]
        noncomm_ring
      _ = 1 + φ (star P + P + P * star P) := by rw [map_add, map_add, map_mul, map_star]
      _ = 1 := by rw [relativeTwoPart_mul_star, map_zero, add_zero]

end Relative

end CoarseAssembly.OperatorKTheory

end

end OAI
