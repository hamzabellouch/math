import OAI.Topology.CoarseAssembly.CycleUnitaryNormalization
import OAI.Topology.CoarseAssembly.RipsScaleCompatibility

namespace OAI

/-! # Unital precomposition commutes with continuous regularization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

theorem OddCycle.eq_of_data (c d : OddCycle A) (hs : c.space = d.space)
    (hr : HEq c.representation d.representation) (ho : HEq c.operator d.operator) : c = d := by
  cases c
  cases d
  cases hs
  cases hr
  cases ho
  rfl

theorem conjugation_refl {H : HilbertSpace} (T : End H) :
    operatorConjugation (LinearIsometryEquiv.refl ℂ H).toLinearIsometry T = T := by
  have he : (LinearIsometryEquiv.refl ℂ H).toLinearIsometry.toContinuousLinearMap =
      (1 : End H) := rfl
  unfold operatorConjugation
  rw [he]
  change (ContinuousLinearMap.id ℂ H).comp (T.comp (ContinuousLinearMap.id ℂ H).adjoint) = T
  rw [ContinuousLinearMap.adjoint_id]
  rfl

def OddCycle.regularize_precomp (c : OddCycle A) (φ : B →⋆ₐ[ℂ] A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).UnitaryEquivalent
      ((c.regularize χ).precomp φ.toNonUnitalStarAlgHom) where
  unitary := LinearIsometryEquiv.refl ℂ c.space
  representation_eq b := by
    change (c.regularize χ).representation (φ b) =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).representation b)
    rw [conjugation_refl]
    change c.representation (φ b) + χ (φ b) • (1 - c.representation 1) =
      c.representation (φ b) + χ (φ b) • (1 - c.representation (φ 1))
    rw [map_one φ]
  operator_eq := by
    change (c.regularize χ).operator =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).operator)
    rw [conjugation_refl]
    have hop :
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).unitalSelfAdjoint (χ.comp φ)).operator) =
          (c.unitalSelfAdjoint χ).operator := by
      rw [OddCycle.unitalSelfAdjoint_operator, OddCycle.unitalSelfAdjoint_operator]
      change symmetricCutDown (c.representation (φ 1)) c.operator =
        symmetricCutDown (c.representation 1) c.operator
      rw [map_one φ]
    exact (boundedTransform_congr hop _ _).symm

theorem OddCycle.regularize_precomp_eq (c : OddCycle A) (φ : B →⋆ₐ[ℂ] A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ) =
      (c.regularize χ).precomp φ.toNonUnitalStarAlgHom := by
  refine OddCycle.eq_of_data
    ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ))
    ((c.regularize χ).precomp φ.toNonUnitalStarAlgHom) rfl ?_ ?_
  · apply heq_of_eq
    apply DFunLike.ext
    intro b
    change c.representation (φ b) + χ (φ b) • (1 - c.representation (φ 1)) =
      c.representation (φ b) + χ (φ b) • (1 - c.representation 1)
    rw [map_one φ]
  · apply heq_of_eq
    have h := (c.regularize_precomp φ χ).operator_eq
    change (c.regularize χ).operator =
      operatorConjugation (LinearIsometryEquiv.refl ℂ c.space).toLinearIsometry
        (show End c.space from ((c.precomp φ.toNonUnitalStarAlgHom).regularize (χ.comp φ)).operator) at h
    rw [conjugation_refl] at h
    exact h.symm

end CoarseAssembly.Analytic

end

end OAI
