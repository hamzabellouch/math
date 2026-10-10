import OAI.Topology.CoarseAssembly.DirectSumIntertwining

namespace OAI

/-! # Orthogonal decompositions lifted to the spatial vertex modules -/

noncomputable section

namespace CoarseAssembly

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem orthogonal_isometries_decompose (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1)
    (T : H →L[ℂ] H) (S : E →L[ℂ] E) (R : F →L[ℂ] F)
    (hV : T.comp V.toContinuousLinearMap = V.toContinuousLinearMap.comp S)
    (hW : T.comp W.toContinuousLinearMap = W.toContinuousLinearMap.comp R) :
    T = operatorConjugation V S + operatorConjugation W R := by
  ext x
  have hx : V (V.toContinuousLinearMap.adjoint x) + W (W.toContinuousLinearMap.adjoint x) = x :=
    DFunLike.congr_fun hex x
  change T x = V (S (V.toContinuousLinearMap.adjoint x)) + W (R (W.toContinuousLinearMap.adjoint x))
  calc
    _ = T (V (V.toContinuousLinearMap.adjoint x) + W (W.toContinuousLinearMap.adjoint x)) :=
      congrArg T hx.symm
    _ = _ := by
      rw [map_add]
      exact congrArg₂ (fun x y : H => x + y)
        (DFunLike.congr_fun hV (V.toContinuousLinearMap.adjoint x))
        (DFunLike.congr_fun hW (W.toContinuousLinearMap.adjoint x))

namespace DiscreteRoe

variable {X : Type*} [DecidableEq X]

omit [CompleteSpace F] [DecidableEq X] in
theorem coefficientIsometry_orthogonal (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hVW : V.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap = 0) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint.comp
      (coefficientIsometry W).toContinuousLinearMap = 0 := by
  ext v x
  change (coefficientIsometry V).toContinuousLinearMap.adjoint (coefficientIsometry W v) x = 0
  rw [coefficientIsometry_adjoint_apply, coefficientIsometry_apply]
  exact DFunLike.congr_fun hVW (v x)

omit [DecidableEq X] in
theorem coefficientIsometry_exhaustive (V : E →ₗᵢ[ℂ] H) (W : F →ₗᵢ[ℂ] H)
    (hex : V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint +
      W.toContinuousLinearMap.comp W.toContinuousLinearMap.adjoint = 1) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.comp
        (coefficientIsometry V).toContinuousLinearMap.adjoint +
      (coefficientIsometry W).toContinuousLinearMap.comp
        (coefficientIsometry W).toContinuousLinearMap.adjoint = 1 := by
  ext v x
  change coefficientIsometry V ((coefficientIsometry V).toContinuousLinearMap.adjoint v) x +
    coefficientIsometry W ((coefficientIsometry W).toContinuousLinearMap.adjoint v) x = v x
  rw [coefficientIsometry_apply, coefficientIsometry_apply,
    coefficientIsometry_adjoint_apply, coefficientIsometry_adjoint_apply]
  exact DFunLike.congr_fun hex (v x)

end DiscreteRoe

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d e : OddCycle C(Point X r, ℂ)}

theorem ripsSpatialOperator_directSum (h : c.IsDirectSum d e)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) (he : e.representation 1 = 1) :
    ripsSpatialOperator r e he =
      operatorConjugation (coefficientIsometry h.left) (ripsSpatialOperator r c hc) +
        operatorConjugation (coefficientIsometry h.right) (ripsSpatialOperator r d hd) :=
  orthogonal_isometries_decompose _ _ (coefficientIsometry_exhaustive h.left h.right h.exhaustive)
    _ _ _ (ripsSpatialOperator_directSum_left r h hc he)
    (ripsSpatialOperator_directSum_right r h hd he)

end Rips
end CoarseAssembly

end

end OAI
