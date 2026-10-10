import OAI.Topology.CoarseAssembly.CayleyNaturality
import Mathlib.Analysis.CStarAlgebra.Unitization

namespace OAI

/-! # The rational boundary under a nonunital spatial homomorphism

The lift `1 + (F - 1)` in a unitization makes the complementary summand
explicit. This is the algebraic input to naturality under isometric spatial
inclusions, which extend an operator by the identity off its image.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def identityUnitization (F : A) : Unitization ℂ A := 1 + ((F - 1 : A) : Unitization ℂ A)

theorem identityUnitization_selfAdjoint (F : A) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (identityUnitization F) :=
  (IsSelfAdjoint.one (Unitization ℂ A)).add
    ((hF.sub (IsSelfAdjoint.one A)).map (Unitization.inrNonUnitalStarAlgHom ℂ A))

def unitizationScalar : Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ A
  map_star' := Unitization.fst_star

def unitizationEval : Unitization ℂ A →⋆ₐ[ℂ] A :=
  Unitization.starLift (NonUnitalStarAlgHom.id ℂ A)

@[simp] theorem unitizationEval_apply (a : Unitization ℂ A) :
    unitizationEval a = algebraMap ℂ A a.fst + a.snd := rfl

@[simp] theorem unitizationScalar_identity (F : A) :
    unitizationScalar (identityUnitization F) = 1 := by
  change (identityUnitization F).fst = 1
  simp only [identityUnitization, Unitization.fst_add, Unitization.fst_one,
    Unitization.fst_inr, add_zero]

@[simp] theorem unitizationEval_identity (F : A) :
    unitizationEval (identityUnitization F) = F := by
  simp only [unitizationEval_apply, identityUnitization, Unitization.fst_add,
    Unitization.fst_one, Unitization.fst_inr, Unitization.snd_add, Unitization.snd_one,
    Unitization.snd_inr, add_zero, zero_add, map_one]
  abel

theorem rationalBoundaryUnitary_identity_scalar (F : A) (hF : IsSelfAdjoint F) :
    (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A).fst = 1 := by
  have h := map_rationalBoundaryUnitary (unitizationScalar (A := A))
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  have hsq : unitizationScalar (identityUnitization F) ^ 2 = (1 : ℂ) := by
    rw [unitizationScalar_identity]
    simp
  have hu := rationalBoundaryUnitary_eq_one _
    ((identityUnitization_selfAdjoint F hF).map (unitizationScalar (A := A))) hsq
  exact h.trans (congrArg (fun u : unitary ℂ => (u : ℂ)) hu)

theorem rationalBoundaryUnitary_identity_eval (F : A) (hF : IsSelfAdjoint F) :
    unitizationEval (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A) =
        (rationalBoundaryUnitary F hF : A) := by
  have h := map_rationalBoundaryUnitary (unitizationEval (A := A))
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  simpa only [unitizationEval_identity] using h

theorem rationalBoundaryUnitary_identity (F : A) (hF : IsSelfAdjoint F) :
    (rationalBoundaryUnitary (identityUnitization F)
      (identityUnitization_selfAdjoint F hF) : Unitization ℂ A) =
        1 + (((rationalBoundaryUnitary F hF : A) - 1 : A) : Unitization ℂ A) := by
  have hs := rationalBoundaryUnitary_identity_scalar F hF
  have he := rationalBoundaryUnitary_identity_eval F hF
  rw [unitizationEval_apply, hs, map_one] at he
  apply Unitization.ext
  · simpa only [Unitization.fst_add, Unitization.fst_one, Unitization.fst_inr,
      add_zero] using hs
  · simpa only [Unitization.snd_add, Unitization.snd_one, Unitization.snd_inr,
      zero_add] using eq_sub_of_add_eq' he

end CoarseAssembly.Analytic

end

end OAI
