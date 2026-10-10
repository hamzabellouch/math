import OAI.Topology.CoarseAssembly.CoefficientDecomposition

namespace OAI

/-! # Extending an orthogonal decomposition by the identity -/

noncomputable section

namespace CoarseAssembly

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_decomposition
    (U : G →ₗᵢ[ℂ] H) (V : E →ₗᵢ[ℂ] G) (W : F →ₗᵢ[ℂ] G)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    isometricExtension U (operatorConjugation V A + operatorConjugation W B) =
      1 + operatorConjugation (U.comp V) (A - 1) + operatorConjugation (U.comp W) (B - 1) := by
  have hone : operatorConjugation V (1 : E →L[ℂ] E) +
      operatorConjugation W (1 : F →L[ℂ] F) = 1 := by
    ext x
    exact DFunLike.congr_fun hex x
  have hinside : (operatorConjugation V A + operatorConjugation W B) - 1 =
      operatorConjugation V (A - 1) + operatorConjugation W (B - 1) := by
    change (operatorConjugationHom V A + operatorConjugationHom W B) - 1 =
      operatorConjugationHom V (A - 1) + operatorConjugationHom W (B - 1)
    rw [map_sub, map_sub, ← hone]
    abel
  change 1 + operatorConjugationHom U ((operatorConjugation V A + operatorConjugation W B) - 1) = _
  rw [hinside, map_add]
  change 1 + (operatorConjugation U (operatorConjugation V (A - 1)) +
    operatorConjugation U (operatorConjugation W (B - 1))) = _
  rw [operatorConjugation_comp, operatorConjugation_comp, add_assoc]

omit [CompleteSpace F] in
theorem isometry_comp_orthogonal
    (U : G →ₗᵢ[ℂ] H) (V : E →ₗᵢ[ℂ] G) (W : F →ₗᵢ[ℂ] G)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0) :
    (U.comp V).toContinuousLinearMap.adjoint.comp (U.comp W).toContinuousLinearMap = 0 := by
  have hV : (U.comp V).toContinuousLinearMap = U.toContinuousLinearMap.comp V.toContinuousLinearMap := rfl
  have hW : (U.comp W).toContinuousLinearMap = U.toContinuousLinearMap.comp W.toContinuousLinearMap := rfl
  rw [hV, hW, ContinuousLinearMap.adjoint_comp]
  ext x
  change V.toContinuousLinearMap.adjoint
    (U.toContinuousLinearMap.adjoint (U (W x))) = 0
  rw [adjoint_apply_isometry]
  exact DFunLike.congr_fun hVW x

end CoarseAssembly

end

end OAI
