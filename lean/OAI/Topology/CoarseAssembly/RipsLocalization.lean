import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsPartition
import OAI.Topology.CoarseAssembly.SpatialLocalization

namespace OAI

/-! # The spatial localization of a unital finite-Rips Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)

omit [DecidableEq X] in
theorem representedSqrt_adjoint (c : OddCycle C(Point X r, ℂ)) (x : X) :
    (representedSqrt r c x).adjoint = representedSqrt r c x := by
  exact ((sqrtCoordinate_selfAdjoint r x).map c.representation).star_eq

omit [DecidableEq X] in
theorem representedSqrt_partition (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    ∑ x, (representedSqrt r c x).adjoint.comp (representedSqrt r c x) = 1 := by
  simp only [representedSqrt_adjoint]
  change (∑ x, c.representation (sqrtCoordinate r x) *
    c.representation (sqrtCoordinate r x)) = 1
  simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]

omit [DecidableEq X] in
theorem representedSqrt_disjoint (c : OddCycle C(Point X r, ℂ))
    (x y : X) (hxy : r < dist x y) :
    representedSqrt r c x * representedSqrt r c y = 0 := by
  change c.representation (sqrtCoordinate r x) * c.representation (sqrtCoordinate r y) = 0
  rw [← map_mul, sqrtCoordinate_mul_eq_zero r x y hxy, map_zero]

theorem ripsCompression_eq_localized (c : OddCycle C(Point X r, ℂ)) :
    partitionCompression (representedSqrt r c) c.operator =
      localizedOperator c (sqrtCoordinate r) := by
  rw [partitionCompression_eq_sum]
  simp only [representedSqrt_adjoint]
  apply Finset.sum_congr rfl
  intro x _
  change (c.representation (sqrtCoordinate r x)).comp
    (c.operator.comp (c.representation (sqrtCoordinate r x))) =
      (c.representation (sqrtCoordinate r x) * c.operator) *
        c.representation (sqrtCoordinate r x)
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

theorem ripsSpatialOperator_propagation (hr : 0 ≤ r) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : PropagationLE (r + r) (ripsSpatialOperator r c hπ) :=
  localizedSpatialOperator_propagation _ _ (representedSqrt_adjoint r c) r hr
    (representedSqrt_disjoint r c) c.operator

theorem ripsSpatialOperator_norm_le (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : ‖ripsSpatialOperator r c hπ‖ ≤ ‖c.operator‖ + 2 :=
  localizedSpatialOperator_norm_le _ _ _

theorem ripsSpatialOperator_selfAdjoint (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (ripsSpatialOperator r c hπ) :=
  localizedSpatialOperator_selfAdjoint _ _ _ hF

theorem ripsCompression_square_compact (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (partitionCompression (representedSqrt r c) c.operator *
      partitionCompression (representedSqrt r c) c.operator - (1 : End c.space)) := by
  have hp : ∑ x, c.representation (sqrtCoordinate r x) *
      c.representation (sqrtCoordinate r x) = 1 := by
    simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]
  let d := localizedCycle c (sqrtCoordinate r) hF (sqrtCoordinate_selfAdjoint r) hp
  have hd := d.square_compact 1
  change IsCompactOperator (((c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator)) *
    (c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator)) - (1 : End c.space)) *
      c.representation 1) at hd
  have he : c.operator + (localizedOperator c (sqrtCoordinate r) - c.operator) =
      localizedOperator c (sqrtCoordinate r) := by abel
  rw [he, hπ, mul_one] at hd
  rw [ripsCompression_eq_localized]
  exact hd

theorem ripsSpatialOperator_square_compact (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (ripsSpatialOperator r c hπ * ripsSpatialOperator r c hπ -
      (1 : Operator X c.space)) :=
  isometricExtension_square_compact _ _ (ripsCompression_square_compact r c hπ hF)

end CoarseAssembly.Rips

end

end OAI
