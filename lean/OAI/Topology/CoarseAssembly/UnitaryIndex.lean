import OAI.Topology.CoarseAssembly.DegenerateCutDown

namespace OAI

/-! # Unitary invariance of the explicit cycle index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : HilbertSpace}

theorem operatorConjugation_equiv (e : H ≃ₗᵢ[ℂ] K) (T : End H) :
    operatorConjugation e.toLinearIsometry T = e.conjStarAlgEquiv T := by
  have he : e.toLinearIsometry.toContinuousLinearMap.adjoint =
      (e.symm : K →L[ℂ] H) := e.adjoint_eq_symm
  ext x
  change e (T (e.toLinearIsometry.toContinuousLinearMap.adjoint x)) = e (T (e.symm x))
  rw [he]
  rfl

theorem symmetricCutDown_map (φ : End H →⋆ₐ[ℂ] End K) (P F : End H) :
    φ (symmetricCutDown P F) = symmetricCutDown (φ P) (φ F) := by
  have hs (r : ℝ) (T : End H) : φ (r • T) = r • φ T := φ.toAlgHom.map_smul_of_tower r T
  unfold symmetricCutDown
  rw [map_add, hs, map_add, map_star,
    map_mul, map_mul, map_sub, map_one]

theorem positiveProjection_map (φ : End H →⋆ₐ[ℂ] End K) (F : End H) :
    φ (positiveProjection F) = positiveProjection (φ F) := by
  have hs (r : ℝ) (T : End H) : φ (r • T) = r • φ T := φ.toAlgHom.map_smul_of_tower r T
  unfold positiveProjection
  rw [hs, map_add, map_one]

theorem toeplitzCompression_map (φ : End H →⋆ₐ[ℂ] End K) (P U : End H) :
    φ (toeplitzCompression P U) = toeplitzCompression (φ P) (φ U) := by
  simp only [toeplitzCompression, map_add, map_mul, map_sub, map_one]

theorem fredholmIndex_conjugation (e : H ≃ₗᵢ[ℂ] K) (T : End H) (hT : T.IsFredholm) :
    (e.conjStarAlgEquiv T).toLinearMap.index = T.toLinearMap.index := by
  have he := e.toContinuousLinearEquiv.isFredholm
  have hei := e.symm.toContinuousLinearEquiv.isFredholm
  have hz : (e.toContinuousLinearEquiv : H →L[ℂ] K).toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.bijective
  have hzi : (e.symm.toContinuousLinearEquiv : K →L[ℂ] H).toLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.symm.bijective
  change ((e.toContinuousLinearEquiv : H →L[ℂ] K) ∘L T ∘L
    (e.symm.toContinuousLinearEquiv : K →L[ℂ] H)).toLinearMap.index = _
  rw [he.index_comp (hT.comp hei), hT.index_comp hei, hz, hzi, zero_add, add_zero]

variable {A : Type} [CStarAlgebra A]

theorem rawCycleToeplitz_unitary (c d : OddCycle A) (h : c.UnitaryEquivalent d) (u : A) :
    rawCycleToeplitz d u = h.unitary.conjStarAlgEquiv (rawCycleToeplitz c u) := by
  let φ : End c.space →⋆ₐ[ℂ] End d.space := h.unitary.conjStarAlgEquiv.toStarAlgHom
  have hrep (a : A) : d.representation a = φ (c.representation a) :=
    (h.representation_eq a).trans (operatorConjugation_equiv h.unitary _)
  have hop : d.operator = φ c.operator :=
    h.operator_eq.trans (operatorConjugation_equiv h.unitary _)
  change rawCycleToeplitz d u = φ (rawCycleToeplitz c u)
  unfold rawCycleToeplitz
  rw [toeplitzCompression_map φ, positiveProjection_map φ, symmetricCutDown_map φ]
  simp only [unitaryExtension, map_add, map_sub, map_one]
  rw [hop, hrep 1, hrep u]

theorem rawCycleIndex_unitary (c d : OddCycle A) (h : c.UnitaryEquivalent d) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) : rawCycleIndex d u = rawCycleIndex c u := by
  unfold rawCycleIndex
  rw [rawCycleToeplitz_unitary c d h u]
  exact fredholmIndex_conjugation h.unitary _ (rawCycleToeplitz_fredholm c u hul hur)

end CoarseAssembly.Analytic

end

end OAI
