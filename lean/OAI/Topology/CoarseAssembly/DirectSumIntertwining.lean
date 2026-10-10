import OAI.Topology.CoarseAssembly.OrthogonalBlock
import OAI.Topology.CoarseAssembly.PartitionIntertwining

namespace OAI

/-! # Direct-sum inclusions intertwine the actual localized operators -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

theorem OddCycle.IsDirectSum.block_apply_left (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) (v : c.space) :
    h.block T S (h.left v) = h.left (T v) := by
  have hz : h.right.toContinuousLinearMap.adjoint (h.left v) = 0 :=
    DFunLike.congr_fun h.orthogonal_reverse v
  change h.left (T (h.left.toContinuousLinearMap.adjoint (h.left v))) +
    h.right (S (h.right.toContinuousLinearMap.adjoint (h.left v))) = _
  rw [adjoint_apply_isometry, hz, map_zero, map_zero, add_zero]

theorem OddCycle.IsDirectSum.block_apply_right (h : c.IsDirectSum d e)
    (T : End c.space) (S : End d.space) (v : d.space) :
    h.block T S (h.right v) = h.right (S v) := by
  have hz : h.left.toContinuousLinearMap.adjoint (h.right v) = 0 :=
    DFunLike.congr_fun h.orthogonal v
  change h.left (T (h.left.toContinuousLinearMap.adjoint (h.right v))) +
    h.right (S (h.right.toContinuousLinearMap.adjoint (h.right v))) = _
  rw [adjoint_apply_isometry, hz, map_zero, map_zero, zero_add]

end CoarseAssembly.Analytic

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d e : OddCycle C(Point X r, ℂ)}

theorem ripsSpatialOperator_directSum_left (h : c.IsDirectSum d e)
    (hc : c.representation 1 = 1) (he : e.representation 1 = 1) :
    (ripsSpatialOperator r e he).comp (coefficientIsometry h.left).toContinuousLinearMap =
      (coefficientIsometry h.left).toContinuousLinearMap.comp (ripsSpatialOperator r c hc) := by
  apply localizedSpatialOperator_intertwines h.left
    (representedSqrt r c) (representedSqrt r e)
    (representedSqrt_adjoint r c) (representedSqrt_adjoint r e)
    (representedSqrt_partition r c hc) (representedSqrt_partition r e he)
  · intro x v
    change e.representation (sqrtCoordinate r x) (h.left v) = _
    rw [h.representation_eq]
    exact h.block_apply_left _ _ v
  · intro v
    rw [h.operator_eq]
    exact h.block_apply_left _ _ v

theorem ripsSpatialOperator_directSum_right (h : c.IsDirectSum d e)
    (hd : d.representation 1 = 1) (he : e.representation 1 = 1) :
    (ripsSpatialOperator r e he).comp (coefficientIsometry h.right).toContinuousLinearMap =
      (coefficientIsometry h.right).toContinuousLinearMap.comp (ripsSpatialOperator r d hd) := by
  apply localizedSpatialOperator_intertwines h.right
    (representedSqrt r d) (representedSqrt r e)
    (representedSqrt_adjoint r d) (representedSqrt_adjoint r e)
    (representedSqrt_partition r d hd) (representedSqrt_partition r e he)
  · intro x v
    change e.representation (sqrtCoordinate r x) (h.right v) = _
    rw [h.representation_eq]
    exact h.block_apply_right _ _ v
  · intro v
    rw [h.operator_eq]
    exact h.block_apply_right _ _ v

end CoarseAssembly.Rips

end

end OAI
