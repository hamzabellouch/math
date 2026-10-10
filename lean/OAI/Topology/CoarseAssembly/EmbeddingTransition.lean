import OAI.Topology.CoarseAssembly.IsometricExtension
import OAI.Topology.CoarseAssembly.CayleyNonunitalNaturality

namespace OAI

/-! # The partial isometry comparing two Hilbert-space embeddings -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def embeddingTransition (V W : E →ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  W.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

theorem embeddingTransition_partial (V W : E →ₗᵢ[ℂ] H) :
    embeddingTransition V W * star (embeddingTransition V W) * embeddingTransition V W =
      embeddingTransition V W := by
  ext x
  simp [embeddingTransition, ContinuousLinearMap.star_eq_adjoint]

theorem embeddingTransition_initial (V W : E →ₗᵢ[ℂ] H) :
    star (embeddingTransition V W) * embeddingTransition V W = operatorConjugation V 1 := by
  ext x
  simp [embeddingTransition, operatorConjugation, ContinuousLinearMap.star_eq_adjoint]

theorem embeddingTransition_support_left (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    (star (embeddingTransition V W) * embeddingTransition V W) * operatorConjugation V a =
      operatorConjugation V a := by
  rw [embeddingTransition_initial, ← operatorConjugation_mul, one_mul]

theorem embeddingTransition_support_right (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    operatorConjugation V a * (star (embeddingTransition V W) * embeddingTransition V W) =
      operatorConjugation V a := by
  rw [embeddingTransition_initial, ← operatorConjugation_mul, mul_one]

theorem embeddingTransition_conjugation (V W : E →ₗᵢ[ℂ] H) (a : E →L[ℂ] E) :
    embeddingTransition V W * operatorConjugation V a * star (embeddingTransition V W) =
      operatorConjugation W a := by
  ext x
  simp [embeddingTransition, operatorConjugation, ContinuousLinearMap.star_eq_adjoint]

theorem rationalBoundaryUnitary_isometricExtension (V : E →ₗᵢ[ℂ] H)
    (F : E →L[ℂ] E) (hF : IsSelfAdjoint F) :
    (Analytic.rationalBoundaryUnitary (isometricExtension V F)
      (isometricExtension_selfAdjoint V F hF) : H →L[ℂ] H) =
        1 + operatorConjugation V ((Analytic.rationalBoundaryUnitary F hF : E →L[ℂ] E) - 1) :=
  (Analytic.nonunital_rationalBoundaryUnitary (operatorConjugationHom V) F hF).symm

end CoarseAssembly

end

end OAI
