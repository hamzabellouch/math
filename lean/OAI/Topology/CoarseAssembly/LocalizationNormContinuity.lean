import OAI.Topology.CoarseAssembly.PartitionCompactPerturbation

namespace OAI

/-! # Localization is contractive in the Fredholm operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem localizedSpatialOperator_sub_norm_le (a : X → E →L[ℂ] E)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (F G : E →L[ℂ] E) :
    ‖localizedSpatialOperator a ha F - localizedSpatialOperator a ha G‖ ≤ ‖F - G‖ := by
  change ‖isometricExtension (partitionIsometry a ha) (partitionCompression a F) -
    isometricExtension (partitionIsometry a ha) (partitionCompression a G)‖ ≤ _
  rw [isometricExtension_sub, partitionCompression_sub]
  exact (operatorConjugation_norm_le _ _).trans (partitionCompression_norm_le a ha (F - G))

omit [Fintype X] [DecidableEq X] in
theorem coefficientExtension_sub_norm_le (V : E →ₗᵢ[ℂ] H) (F G : Operator X E) :
    ‖coefficientExtension V F - coefficientExtension V G‖ ≤ ‖F - G‖ := by
  change ‖isometricExtension (coefficientIsometry V) F - isometricExtension (coefficientIsometry V) G‖ ≤ _
  rw [isometricExtension_sub]
  exact operatorConjugation_norm_le _ _

end CoarseAssembly.DiscreteRoe

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)

theorem ampleRipsOperator_homotopy_norm_le (h : OddHomotopy C(Point X r, ℂ))
    (s t : Interval) (hs : (h.eval s).representation 1 = 1) (ht : (h.eval t).representation 1 = 1)
    (hrep : h.representation s = h.representation t) :
    ‖ampleRipsOperator r (h.eval s) hs - ampleRipsOperator r (h.eval t) ht‖ ≤
      ‖h.operator s - h.operator t‖ := by
  apply (coefficientExtension_sub_norm_le (ampleIsometry h.space) _ _).trans
  have heq : (show X → End h.space from representedSqrt r (h.eval s)) =
      (show X → End h.space from representedSqrt r (h.eval t)) := by
    funext x
    exact congrArg (fun ρ => ρ (sqrtCoordinate r x)) hrep
  change ‖(show Operator X h.space from
      localizedSpatialOperator (representedSqrt r (h.eval s)) _ (h.operator s)) -
    (show Operator X h.space from
      localizedSpatialOperator (representedSqrt r (h.eval t)) _ (h.operator t))‖ ≤ _
  simp only [heq]
  exact localizedSpatialOperator_sub_norm_le _ _ _ _

end CoarseAssembly.Rips

end

end OAI
