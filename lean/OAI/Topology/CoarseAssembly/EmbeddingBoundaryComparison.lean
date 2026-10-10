import OAI.Topology.CoarseAssembly.EmbeddingTransition
import OAI.Topology.CoarseAssembly.RelativePartialIsometry
import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass

namespace OAI

/-! # Equality of Roe boundary classes from two embeddings of one operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic OperatorKTheory

variable {X E H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem multiplierBoundaryUnitary_embedding (V : E →ₗᵢ[ℂ] Module X H)
    (S : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFV : F.val = isometricExtension V S) :
    (multiplierBoundaryUnitary F hF : Operator X H) - 1 =
      operatorConjugation V ((rationalBoundaryUnitary S hS : E →L[ℂ] E) - 1) := by
  have hm := map_rationalBoundaryUnitary
    (multiplierAlgebra (X := X) (H := H)).subtype F hF
  change (multiplierBoundaryUnitary F hF : Operator X H) =
    (rationalBoundaryUnitary F.val (hF.map (multiplierAlgebra (X := X) (H := H)).subtype) :
      Operator X H) at hm
  simp only [hFV] at hm
  rw [rationalBoundaryUnitary_isometricExtension V S hS] at hm
  rw [hm, add_sub_cancel_left]

/-- Two embeddings of the same operator give the same class whenever their
transition is a Roe multiplier. Coefficient embeddings satisfy this via propagation zero. -/
theorem multiplierBoundaryClass_embedding
    (V W : E →ₗᵢ[ℂ] Module X H) (S : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (F G : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hFV : F.val = isometricExtension V S) (hGW : G.val = isometricExtension W S)
    (hVW : RoeMultiplier (embeddingTransition V W)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  let T : multiplierAlgebra (X := X) (H := H) := ⟨embeddingTransition V W, hVW⟩
  let u := rationalBoundaryUnitary F hF
  let v := rationalBoundaryUnitary G hG
  let a := (rationalBoundaryUnitary S hS : E →L[ℂ] E) - 1
  have hu : (u : multiplierAlgebra (X := X) (H := H)).val - 1 = operatorConjugation V a :=
    multiplierBoundaryUnitary_embedding V S hS F hF hFV
  have hv : (v : multiplierAlgebra (X := X) (H := H)).val - 1 = operatorConjugation W a :=
    multiplierBoundaryUnitary_embedding W S hS G hG hGW
  have hT : T * star T * T = T := by
    apply Subtype.ext
    exact embeddingTransition_partial V W
  have hl : (star T * T) * ((u : multiplierAlgebra (X := X) (H := H)) - 1) =
      (u : multiplierAlgebra (X := X) (H := H)) - 1 := by
    apply Subtype.ext
    change (star (embeddingTransition V W) * embeddingTransition V W) *
      ((u : multiplierAlgebra (X := X) (H := H)).val - 1) =
        (u : multiplierAlgebra (X := X) (H := H)).val - 1
    rw [hu]
    exact embeddingTransition_support_left V W a
  have hr : ((u : multiplierAlgebra (X := X) (H := H)) - 1) * (star T * T) =
      (u : multiplierAlgebra (X := X) (H := H)) - 1 := by
    apply Subtype.ext
    change ((u : multiplierAlgebra (X := X) (H := H)).val - 1) *
      (star (embeddingTransition V W) * embeddingTransition V W) =
        (u : multiplierAlgebra (X := X) (H := H)).val - 1
    rw [hu]
    exact embeddingTransition_support_right V W a
  have he : (v : multiplierAlgebra (X := X) (H := H)) =
      1 + T * ((u : multiplierAlgebra (X := X) (H := H)) - 1) * star T := by
    apply Subtype.ext
    change (v : multiplierAlgebra (X := X) (H := H)).val =
      1 + embeddingTransition V W * ((u : multiplierAlgebra (X := X) (H := H)).val - 1) *
        star (embeddingTransition V W)
    rw [hu, embeddingTransition_conjugation]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hv)
  let φ := (multiplierAlgebra (X := X) (H := H)).subtype
  exact relativeClass_partialIsometry (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) φ continuous_subtype_val
    (fun b c hc => b.property ⟨c, hc⟩) T hT u v hl hr he
    (multiplierBoundaryUnitary_sub_one_mem F hF hFd)
    (multiplierBoundaryUnitary_sub_one_mem G hG hGd)

end CoarseAssembly.DiscreteRoe

end

end OAI
