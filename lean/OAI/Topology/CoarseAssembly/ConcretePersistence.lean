import OAI.Topology.CoarseAssembly.HexagonSides
import OAI.Topology.CoarseAssembly.FiberedPersistence
import OAI.Topology.CoarseAssembly.KazhdanInput

namespace OAI

/-! # Persistence with the geometric boundary input discharged

The actual six-side boundary walks are now substituted into the graph-family
detector. Only the stated published circle pairing and countable-additivity
inputs remain in the nonvanishing conclusions.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance concretePersistenceMetric1 : MetricSpace FiberedUnion := componentUnionMetric elementaryMoves chosenHolonomyUnit

def concreteFiberClass (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) : KX1 FiberedUnion :=
  fiberedBoundaryClass elementaryMoves
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) input hadd

theorem concreteFiberClass_infinite_order (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (n : ℤ) (hn : n ≠ 0) :
    n • concreteFiberClass input hadd ≠ 0 :=
  fiberedBoundaryClass_infinite_order elementaryMoves
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) input hadd
    (hexagonalBoundaryWalks.fiber_charge_one elementaryMoves chosenHolonomyUnit) n hn

theorem concreteFiberClass_rational_ne_zero (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) :
    (1 : ℚ) ⊗ₜ[ℤ] concreteFiberClass input hadd ≠ 0 :=
  rationalization_ne_zero _ (concreteFiberClass_infinite_order input hadd)

end CoarseAssembly

end

end OAI
