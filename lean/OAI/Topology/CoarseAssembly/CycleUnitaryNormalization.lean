import OAI.Topology.CoarseAssembly.RegularizedCycle
import OAI.Topology.CoarseAssembly.BoundedTransformNaturality

namespace OAI

/-! # Unitary equivalence is preserved by explicit cycle normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

theorem unitaryConjugation_eq (U : H ≃ₗᵢ[ℂ] K) (F : End H) :
    U.conjStarAlgEquiv.toStarAlgHom F = operatorConjugation U.toLinearIsometry F := by
  have hadj : U.toLinearIsometry.toContinuousLinearMap.adjoint =
      U.symm.toLinearIsometry.toContinuousLinearMap := U.adjoint_eq_symm
  change U.toLinearIsometry.toContinuousLinearMap.comp
      (F.comp U.symm.toLinearIsometry.toContinuousLinearMap) =
    U.toLinearIsometry.toContinuousLinearMap.comp
      (F.comp U.toLinearIsometry.toContinuousLinearMap.adjoint)
  rw [hadj]

variable {A : Type} [CStarAlgebra A] {c d : OddCycle A}

def OddCycle.UnitaryEquivalent.regularize (e : c.UnitaryEquivalent d) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).UnitaryEquivalent (d.regularize χ) where
  unitary := e.unitary
  representation_eq a := by
    let φ : End c.space →⋆ₐ[ℂ] End d.space := e.unitary.conjStarAlgEquiv.toStarAlgHom
    have hφ (T : End c.space) : φ T = operatorConjugation e.unitary.toLinearIsometry T :=
      unitaryConjugation_eq _ _
    have hr (a : A) : φ (c.representation a) = d.representation a :=
      (hφ _).trans (e.representation_eq a).symm
    change d.representation a + χ a • (1 - d.representation 1) =
      operatorConjugation e.unitary.toLinearIsometry
        (c.representation a + χ a • (1 - c.representation 1))
    rw [← hφ]
    simp only [map_add, map_smul, map_sub, map_one, hr]
  operator_eq := by
    let φ : End c.space →⋆ₐ[ℂ] End d.space := e.unitary.conjStarAlgEquiv.toStarAlgHom
    have hφ (T : End c.space) : φ T = operatorConjugation e.unitary.toLinearIsometry T :=
      unitaryConjugation_eq _ _
    have hr : φ (c.representation 1) = d.representation 1 :=
      (hφ _).trans (e.representation_eq 1).symm
    have hF : φ c.operator = d.operator := (hφ _).trans e.operator_eq.symm
    have hG : (d.unitalSelfAdjoint χ).operator = φ (c.unitalSelfAdjoint χ).operator := by
      rw [d.unitalSelfAdjoint_operator, c.unitalSelfAdjoint_operator, map_symmetricCutDown, hr, hF]
    change boundedTransform (d.unitalSelfAdjoint χ).operator _ =
      operatorConjugation e.unitary.toLinearIsometry
        (boundedTransform (c.unitalSelfAdjoint χ).operator _)
    rw [← hφ]
    erw [map_boundedTransform]
    exact boundedTransform_congr hG _ _

end CoarseAssembly.Analytic

end

end OAI
