import OAI.Topology.CoarseAssembly.RipsLocalization
import OAI.Topology.CoarseAssembly.RipsEmbedding
import OAI.Topology.CoarseAssembly.PartitionInclusion

namespace OAI

/-! # Finite-Rips localization respects an actual vertex inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (r : ℝ) (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)

def inclusionFunctionHom : C(Point Y r, ℂ) →⋆ₐ[ℂ] C(Point X r, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨mapPoint e he, mapPoint_continuous e he⟩

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem inclusionFunctionHom_sqrt (x : X) :
    inclusionFunctionHom r e he (sqrtCoordinate r (e x)) = sqrtCoordinate r x := by
  ext p
  change (Real.sqrt ((mapPoint e he p).weight (e x)) : ℂ) = _
  rw [mapPoint_weight_self]
  rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem inclusionFunctionHom_sqrt_zero (y : Y) (hy : y ∉ Set.range e) :
    inclusionFunctionHom r e he (sqrtCoordinate r y) = 0 := by
  ext p
  change (Real.sqrt ((mapPoint e he p).weight y) : ℂ) = 0
  rw [show (mapPoint e he p).weight y = 0 from
    Finsupp.embDomain_of_notMem_range e p.weight y hy]
  simp

def includedCycle (c : OddCycle C(Point X r, ℂ)) : OddCycle C(Point Y r, ℂ) :=
  c.precomp (inclusionFunctionHom r e he).toNonUnitalStarAlgHom

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_unital (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    (includedCycle r e he c).representation 1 = 1 := by
  change c.representation (inclusionFunctionHom r e he 1) = 1
  rw [map_one, hπ]

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_representedSqrt (c : OddCycle C(Point X r, ℂ)) (x : X) :
    representedSqrt r (includedCycle r e he c) (e x) = representedSqrt r c x := by
  change c.representation (inclusionFunctionHom r e he (sqrtCoordinate r (e x))) = _
  rw [inclusionFunctionHom_sqrt]
  rfl

omit [DecidableEq X] [DecidableEq Y] in
theorem includedCycle_representedSqrt_zero (c : OddCycle C(Point X r, ℂ))
    (y : Y) (hy : y ∉ Set.range e) :
    representedSqrt r (includedCycle r e he c) y = 0 := by
  change c.representation (inclusionFunctionHom r e he (sqrtCoordinate r y)) = 0
  rw [inclusionFunctionHom_sqrt_zero r e he y hy, map_zero]

theorem ripsSpatialOperator_inclusion (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    ripsSpatialOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ) =
      isometricExtension (inclusionIsometry e) (ripsSpatialOperator r c hπ) := by
  exact localizedSpatialOperator_inclusion e (representedSqrt r c)
    (representedSqrt r (includedCycle r e he c)) (representedSqrt_partition r c hπ)
    (representedSqrt_partition r (includedCycle r e he c) (includedCycle_unital r e he c hπ))
    (includedCycle_representedSqrt r e he c)
    (includedCycle_representedSqrt_zero r e he c) c.operator

end CoarseAssembly.Rips

end

end OAI
