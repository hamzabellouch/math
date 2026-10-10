import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CycleCompactPerturbation

namespace OAI

/-! # Extending a Fredholm operator by the identity off an isometric image -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_selfAdjoint (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E)
    (hF : IsSelfAdjoint F) : IsSelfAdjoint (isometricExtension V F) :=
  (IsSelfAdjoint.one (H →L[ℂ] H)).add
    ((hF.sub (IsSelfAdjoint.one (E →L[ℂ] E))).map
      (operatorConjugationHom V))

theorem isometricExtension_square_defect (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    isometricExtension V F * isometricExtension V F - 1 =
      operatorConjugation V (F * F - 1) := by
  let φ := operatorConjugationHom V
  have he : (F - 1) * (F - 1) + (F - 1) + (F - 1) = F * F - 1 := by noncomm_ring
  calc
    isometricExtension V F * isometricExtension V F - 1 =
        φ (F - 1) * φ (F - 1) + φ (F - 1) + φ (F - 1) := by
      change (1 + φ (F - 1)) * (1 + φ (F - 1)) - 1 = _
      noncomm_ring
    _ = φ ((F - 1) * (F - 1) + (F - 1) + (F - 1)) := by
      rw [map_add, map_add, map_mul]
    _ = operatorConjugation V (F * F - 1) := by rw [he]; rfl

theorem isometricExtension_square_compact (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E)
    (hF : IsCompactOperator (F * F - (1 : E →L[ℂ] E))) :
    IsCompactOperator (isometricExtension V F * isometricExtension V F -
      (1 : H →L[ℂ] H)) := by
  rw [isometricExtension_square_defect]
  exact (hF.comp_clm V.toContinuousLinearMap.adjoint).clm_comp V.toContinuousLinearMap

theorem operatorConjugation_norm_le (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    ‖operatorConjugation V F‖ ≤ ‖F‖ := by
  have hV := V.norm_toContinuousLinearMap_le
  have hVs : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  have h1 : ‖V.toContinuousLinearMap.comp F‖ ≤ ‖V.toContinuousLinearMap‖ * ‖F‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖(V.toContinuousLinearMap.comp F).comp V.toContinuousLinearMap.adjoint‖ ≤
      ‖V.toContinuousLinearMap.comp F‖ * ‖V.toContinuousLinearMap.adjoint‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖operatorConjugation V F‖ ≤
        ‖V.toContinuousLinearMap‖ * ‖F‖ * ‖V.toContinuousLinearMap.adjoint‖ :=
      h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ ≤ 1 * ‖F‖ * 1 := by gcongr
    _ = ‖F‖ := by ring

theorem isometricExtension_norm_le (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    ‖isometricExtension V F‖ ≤ ‖F‖ + 2 := by
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hd : ‖F - 1‖ ≤ ‖F‖ + 1 := (norm_sub_le _ _).trans (add_le_add le_rfl h1)
  calc
    ‖isometricExtension V F‖ ≤ ‖(1 : H →L[ℂ] H)‖ + ‖operatorConjugation V (F - 1)‖ :=
      norm_add_le _ _
    _ ≤ 1 + ‖F - 1‖ := add_le_add ContinuousLinearMap.norm_id_le
      (operatorConjugation_norm_le V _)
    _ ≤ 1 + (‖F‖ + 1) := add_le_add le_rfl hd
    _ = ‖F‖ + 2 := by ring

end CoarseAssembly

end

end OAI
