import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.AveragingPropagation

namespace OAI

/-! # The fixed published spectral-gap input

The elementary matrices below and their inverses give a fixed finite
symmetric generating set of SL3(Z), with the identity included. The input
used in the conditional development is exactly the uniform lazy-averaging
estimate on the finite congruence quotients, with the standard ample
coefficient space. It is the specialization of Bekka–de la Harpe–Valette
(2008), Proposition 1.3.2 and Example 1.7.4, explained in manuscript §5.2.

No proof of that published input is asserted during the conditional phase.
The spatial Roe transfer itself is proved from it below.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem elementaryMoves_nonempty : elementaryMoves.Nonempty :=
  ⟨1, one_mem_symmetricMoves _⟩

theorem elementaryMoves_symmetric {s : ArithmeticGroup} (hs : s ∈ elementaryMoves) :
    s⁻¹ ∈ elementaryMoves := inv_mem_symmetricMoves hs

def PublishedKazhdanInput : Prop := UniformAveragingGap elementaryMoves AmpleSpace

/-- The transfer in manuscript §5 for the fixed graph family, conditional
only on its identified published spectral-gap input. -/
theorem roe_transfer_of_published_gap (hgap : PublishedKazhdanInput) :
    letI : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit
    DiscreteRoe.MapsToRoe (fiberEmbedding (H := AmpleSpace) BaseFiber) :=
  concrete_transfer_of_gap elementaryMoves chosenHolonomyUnit elementaryMoves_nonempty hgap

end CoarseAssembly

end

end OAI
