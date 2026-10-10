import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ProjectionBlocks
import OAI.Topology.CoarseAssembly.SpatialLocalization

namespace OAI

/-! # Isometric changes of the coefficient Hilbert space

Changing coefficients by a pointwise isometry preserves propagation.
Extending by the identity on its orthogonal complement preserves compact
square defects, as required to place localized cycles on an ample module.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq X] [CompleteSpace E] [CompleteSpace H] in
@[simp] theorem coefficientIsometry_apply (V : E →ₗᵢ[ℂ] H) (v : Module X E) (x : X) :
    coefficientIsometry V v x = V (v x) := rfl

omit [DecidableEq X] in
@[simp] theorem coefficientIsometry_adjoint_apply (V : E →ₗᵢ[ℂ] H)
    (v : Module X H) (x : X) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint v x =
      V.toContinuousLinearMap.adjoint (v x) := by
  rw [coefficientIsometry, blockIsometry_toCLM, blockOperator_adjoint]
  rfl

theorem coefficientIsometry_adjoint_single (V : E →ₗᵢ[ℂ] H) (x : X) (h : H) :
    (coefficientIsometry (X := X) V).toContinuousLinearMap.adjoint (lp.single 2 x h) =
      lp.single 2 x (V.toContinuousLinearMap.adjoint h) := by
  apply lp.ext
  funext y
  simp only [coefficientIsometry_adjoint_apply, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp

theorem coefficientConjugation_entry (V : E →ₗᵢ[ℂ] H) (T : Operator X E) (x y : X) :
    entry (operatorConjugation (coefficientIsometry V) T) x y =
      V.toContinuousLinearMap.comp ((entry T x y).comp V.toContinuousLinearMap.adjoint) := by
  ext h
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply,
    coefficientIsometry_adjoint_single, LinearIsometry.coe_toContinuousLinearMap,
    coefficientIsometry_apply]

variable [PseudoMetricSpace X]

theorem coefficientConjugation_propagation (V : E →ₗᵢ[ℂ] H) {T : Operator X E}
    {r : ℝ} (hp : PropagationLE r T) :
    PropagationLE r (operatorConjugation (coefficientIsometry V) T) := by
  intro x y hxy
  rw [coefficientConjugation_entry, hp x y hxy]
  simp

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_selfAdjoint (V : E →ₗᵢ[ℂ] H) (T : Operator X E)
    (hs : IsSelfAdjoint T) : IsSelfAdjoint (coefficientExtension V T) :=
  isometricExtension_selfAdjoint _ _ hs

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_norm_le (V : E →ₗᵢ[ℂ] H) (T : Operator X E) :
    ‖coefficientExtension V T‖ ≤ ‖T‖ + 2 := isometricExtension_norm_le _ _

omit [DecidableEq X] [PseudoMetricSpace X] in
theorem coefficientExtension_square_compact (V : E →ₗᵢ[ℂ] H) (T : Operator X E)
    (hsq : IsCompactOperator (T * T - (1 : Operator X E))) :
    IsCompactOperator (coefficientExtension V T * coefficientExtension V T -
      (1 : Operator X H)) := isometricExtension_square_compact _ _ hsq

theorem coefficientExtension_propagation (V : E →ₗᵢ[ℂ] H) {T : Operator X E}
    {r : ℝ} (hr : 0 ≤ r) (hp : PropagationLE r T) :
    PropagationLE r (coefficientExtension V T) := by
  have he : coefficientExtension V T = 1 +
      operatorConjugation (coefficientIsometry V) T -
        operatorConjugation (coefficientIsometry V) 1 := by
    change 1 + operatorConjugation (coefficientIsometry V) (T - 1) = _
    simp only [operatorConjugation, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
    abel
  have h1 := propagationLE_one (X := X) (H := H)
  have h2 := coefficientConjugation_propagation V hp
  have h3 := coefficientConjugation_propagation (X := X) V (propagationLE_one (X := X) (H := E))
  have hn : PropagationLE 0 (-operatorConjugation (coefficientIsometry (X := X) V) 1) := by
    convert h3.smul (-1 : ℂ) using 1
    ext v
    simp
  rw [he, sub_eq_add_neg]
  simpa only [max_eq_right hr, max_eq_left hr] using (h1.add h2).add hn

end CoarseAssembly.DiscreteRoe

end

end OAI
