import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

/-!
# Conjugation by an isometry

The spatial operator homomorphism and exact boundary factorization used in
§§5--6 of the coarse Novikov manuscript. Restriction of this homomorphism to
the Roe algebras is a separate range-membership obligation.
-/

namespace CoarseAssembly

variable {E F H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem adjoint_apply_isometry (V : E →ₗᵢ[ℂ] F) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using DFunLike.congr_fun V.adjoint_comp_self x

theorem operatorConjugation_mul (V : E →ₗᵢ[ℂ] F) (T S : E →L[ℂ] E) :
    operatorConjugation V (T * S) = operatorConjugation V T * operatorConjugation V S := by
  ext x
  simp [operatorConjugation]

theorem operatorConjugation_injective (V : E →ₗᵢ[ℂ] F) :
    Function.Injective (operatorConjugation V) := by
  intro T S h
  ext x
  have hx := DFunLike.congr_fun h (V x)
  simpa [operatorConjugation] using V.injective hx

theorem operatorConjugation_star (V : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    operatorConjugation V (star T) = star (operatorConjugation V T) := by
  simp [operatorConjugation, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

theorem operatorConjugation_comp (V : F →ₗᵢ[ℂ] H) (W : E →ₗᵢ[ℂ] F)
    (T : E →L[ℂ] E) :
    operatorConjugation V (operatorConjugation W T) = operatorConjugation (V.comp W) T := by
  have hcomp : (V.comp W).toContinuousLinearMap =
      V.toContinuousLinearMap.comp W.toContinuousLinearMap := rfl
  simp [operatorConjugation, hcomp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]

end CoarseAssembly

end OAI
