import OAI.Topology.CoarseAssembly.OrthogonalExtensionBoundary
import OAI.Topology.CoarseAssembly.EmbeddingBoundaryComparison

namespace OAI

/-! # Addition of actual Roe boundaries supported in orthogonal images -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorConjugation_orthogonal (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    operatorConjugation V A * operatorConjugation W B = 0 := by
  ext x
  change V (A (V.toContinuousLinearMap.adjoint (W (B (W.toContinuousLinearMap.adjoint x))))) = 0
  have hz : V.toContinuousLinearMap.adjoint (W (B (W.toContinuousLinearMap.adjoint x))) = 0 :=
    DFunLike.congr_fun hVW _
  rw [hz, map_zero, map_zero]

namespace DiscreteRoe

open Analytic OperatorKTheory

variable {X : Type*} [DecidableEq X] [PseudoMetricSpace X]

theorem multiplierBoundaryUnitary_eq_raw
    (T : multiplierAlgebra (X := X) (H := H)) (hT : IsSelfAdjoint T) :
    (multiplierBoundaryUnitary T hT : Operator X H) =
      (rationalBoundaryUnitary T.val (hT.map (multiplierAlgebra (X := X) (H := H)).subtype) :
        Operator X H) :=
  map_rationalBoundaryUnitary (multiplierAlgebra (X := X) (H := H)).subtype T hT

/-- The complementary target summand carries the identity; the two supported
boundary classes therefore add in the actual Roe K₁ group. -/
theorem multiplierBoundaryClass_orthogonalEmbeddings
    (V : E →ₗᵢ[ℂ] Module X H) (W : F →ₗᵢ[ℂ] Module X H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (T L R : multiplierAlgebra (X := X) (H := H))
    (hT : IsSelfAdjoint T) (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R)
    (hTd : T.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hLd : L.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hRd : R.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hLV : L.val = isometricExtension V A) (hRW : R.val = isometricExtension W B)
    (hTVW : T.val = 1 + operatorConjugation V (A - 1) + operatorConjugation W (B - 1)) :
    multiplierBoundaryClass T hT hTd =
      multiplierBoundaryClass L hL hLd + multiplierBoundaryClass R hR hRd := by
  let φ := operatorConjugationHom V
  let ψ := operatorConjugationHom W
  have horth : ∀ a b, φ a * ψ b = 0 := operatorConjugation_orthogonal V W hVW
  let σ := nonunitalOrthogonalSumHom φ ψ horth
  have ht : T.val = nonunitalIdentityExtension σ (A, B) := by
    change T.val = 1 + (operatorConjugation V (A - 1) + operatorConjugation W (B - 1))
    simpa only [add_assoc] using hTVW
  have huT := multiplierBoundaryUnitary_eq_raw T hT
  simp only [ht] at huT
  have hprod := rationalBoundaryUnitary_orthogonalExtension φ ψ horth A B hA hB
  have huL : (multiplierBoundaryUnitary L hL : Operator X H) =
      (nonunitalUnitaryExtension φ (rationalBoundaryUnitary A hA) : Operator X H) := by
    have h := multiplierBoundaryUnitary_embedding V A hA L hL hLV
    change (multiplierBoundaryUnitary L hL : Operator X H) =
      1 + operatorConjugation V ((rationalBoundaryUnitary A hA : E →L[ℂ] E) - 1)
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  have huR : (multiplierBoundaryUnitary R hR : Operator X H) =
      (nonunitalUnitaryExtension ψ (rationalBoundaryUnitary B hB) : Operator X H) := by
    have h := multiplierBoundaryUnitary_embedding W B hB R hR hRW
    change (multiplierBoundaryUnitary R hR : Operator X H) =
      1 + operatorConjugation W ((rationalBoundaryUnitary B hB : F →L[ℂ] F) - 1)
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  have hu : multiplierBoundaryUnitary T hT = multiplierBoundaryUnitary L hL *
      multiplierBoundaryUnitary R hR := by
    apply Subtype.ext
    rw [huT]
    have hp := congrArg (fun u : unitary (Operator X H) => u.val) hprod
    change _ = (multiplierBoundaryUnitary L hL : Operator X H) *
      (multiplierBoundaryUnitary R hR : Operator X H)
    rw [huL, huR]
    exact hp
  have h := relativeClass_mul (hS := algebra_isClosed) (algebra (X := X) (H := H))
    (multiplierBoundaryUnitary L hL) (multiplierBoundaryUnitary R hR)
    (multiplierBoundaryUnitary_sub_one_mem L hL hLd)
    (multiplierBoundaryUnitary_sub_one_mem R hR hRd)
  simpa only [multiplierBoundaryClass, ← hu] using h

end DiscreteRoe
end CoarseAssembly

end

end OAI
