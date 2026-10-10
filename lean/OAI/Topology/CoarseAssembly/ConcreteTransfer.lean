import OAI.Topology.CoarseAssembly.ConcreteTransferMaps

namespace OAI

/-! # The transfer on the actual coarse spaces

All metric and inter-fiber hypotheses have been discharged. Only the
averaging projection approximation remains in this intermediate theorem;
it is an own-paper obligation, not an assumed published theorem.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

theorem UniformFiniteBalls.finite_closedBall {X : Type*} [PseudoMetricSpace X]
    (hX : UniformFiniteBalls X) (x : X) (r : ℝ) : (Metric.closedBall x r).Finite := by
  by_cases hr : 0 ≤ r
  · obtain ⟨N, hN⟩ := hX r hr
    obtain ⟨b, hb, hcard⟩ := hN x
    apply b.finite_toSet.subset
    intro y hy
    exact (hb y).mpr (by simpa only [Metric.mem_closedBall, dist_comm] using hy)
  · have he : Metric.closedBall x r = ∅ := Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)
    rw [he]
    exact Set.finite_empty

theorem concrete_transfer_of_approximation
    (S : Finset Congruence.ArithmeticGroup) (t : ℤ_[2]ˣ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Pn : ℕ → Operator VertexUnion H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds (fiberProjection BaseFiber))) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    (∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n)) →
      MapsToRoe (fiberEmbedding (H := H) BaseFiber) := by
  classical
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro hprop
  have hX : ∀ x : VertexUnion, ∀ r : ℝ, (Metric.closedBall x r).Finite :=
    (vertexUnion_uniform_balls S t).finite_closedBall
  exact finite_fiber_transfer (D := BaseUnion) (Q := BaseFiber) (H := H)
    baseUnion_uniform_balls hX (concrete_controlled_fiber_maps S t) Pn hlim hprop

end CoarseAssembly

end

end OAI
