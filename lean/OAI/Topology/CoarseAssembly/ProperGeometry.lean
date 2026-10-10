import OAI.Topology.CoarseAssembly.ConcreteTransfer
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Properness of the concrete coarse spaces

The proved finite-ball estimates imply compact closed balls in the actual
shortest-path metrics. No completion or change of metric is involved.
-/

noncomputable section

namespace CoarseAssembly

theorem UniformFiniteBalls.properSpace {X : Type*} [PseudoMetricSpace X]
    (hX : UniformFiniteBalls X) : ProperSpace X :=
  ⟨fun x r => (hX.finite_closedBall x r).isCompact⟩

theorem baseUnion_proper : ProperSpace BaseUnion :=
  baseUnion_uniform_balls.properSpace

theorem vertexUnion_proper (S : Finset Congruence.ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @ProperSpace VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace :=
  @UniformFiniteBalls.properSpace VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace
    (vertexUnion_uniform_balls S t)

end CoarseAssembly

end

end OAI
