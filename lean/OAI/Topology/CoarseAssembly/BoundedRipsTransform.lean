import OAI.Topology.CoarseAssembly.BoundedCycleTransform
import OAI.Topology.CoarseAssembly.ControlledRipsCycles
import OAI.Topology.CoarseAssembly.RipsFamilyCompactPerturbation

namespace OAI

/-! # Normalizing a bounded Rips cycle family preserves its actual Roe boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ampleRipsOperator_bounded_sub_compact (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    IsCompactOperator (ampleRipsOperator r (c.bounded hπ hs) hπ - ampleRipsOperator r c hπ) := by
  change IsCompactOperator
    (isometricExtension (coefficientIsometry (ampleIsometry c.space))
      (localizedSpatialOperator (representedSqrt r c) (representedSqrt_partition r c hπ)
        (boundedTransform c.operator hs)) -
    isometricExtension (coefficientIsometry (ampleIsometry c.space))
      (localizedSpatialOperator (representedSqrt r c) (representedSqrt_partition r c hπ) c.operator))
  apply isometricExtension_sub_compact
  exact localizedSpatialOperator_sub_compact _ _ _ _ (c.boundedTransform_compact hπ hs)

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

def ControlledCycleFamily.bounded (c : ControlledCycleFamily Q r) : ControlledCycleFamily Q r where
  cycle i := (c.cycle i).bounded (c.unital i) (c.selfAdjoint i)
  unital := c.unital
  selfAdjoint _ := boundedTransform_selfAdjoint _ _
  bound := 1
  bound_nonneg := zero_le_one
  norm_le _ := boundedTransform_norm_le _ _

theorem ControlledCycleFamily.bounded_boundary (c : ControlledCycleFamily Q r)
    (o : ∀ i, Q i) (hr : 0 ≤ r) : c.bounded.boundary o hr = c.boundary o hr := by
  let := separatedMetric o
  exact ampleRipsFamilyBoundary_eq_of_compact o r hr _ _ _ _ _ _ _ _ _ _ _ _
    (fun i => ampleRipsOperator_bounded_sub_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))

end CoarseAssembly.Rips

end

end OAI
