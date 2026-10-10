import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Differential
import OAI.Topology.ArtinGroups.Complexes.Middle
import OAI.Topology.ArtinGroups.Complexes.Subrepresentation
import OAI.Topology.ArtinGroups.Cancellation.Remainder
import OAI.Topology.ArtinGroups.Harmonic.CartanPairingSymm
import OAI.Topology.ArtinGroups.Cancellation.CornerInverse
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistHomotopy
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential
import OAI.Topology.ArtinGroups.Complexes.MinimalEmbedding
import OAI.Topology.ArtinGroups.Complexes.Test
import OAI.Topology.ArtinGroups.Complexes.InverseTwistMap
import OAI.Topology.ArtinGroups.Complexes.CorrectionBoundary
import OAI.Topology.ArtinGroups.Complexes.FrameModelNegativeHom
import OAI.Topology.ArtinGroups.Complexes.FrameCappedInjection
import OAI.Topology.ArtinGroups.Complexes.CoefficientIncoming
import OAI.Topology.ArtinGroups.Harmonic.SwitchIndex
import OAI.Topology.ArtinGroups.Functors.Path
import OAI.Topology.ArtinGroups.Functors.TestIndex
import OAI.Topology.ArtinGroups.Complexes.PureSupportedCycles
import OAI.Topology.ArtinGroups.Functors.SupportedCycles
import OAI.Topology.ArtinGroups.Complexes.ReindexConeIsomorphism
import OAI.Topology.ArtinGroups.Functors.ComplexPureLayer
import OAI.Topology.ArtinGroups.Diagrams.Circle
import OAI.Topology.ArtinGroups.Harmonic.FusionOrbitCapMove
import OAI.Topology.ArtinGroups.Complexes.LowMatrix
import OAI.Topology.ArtinGroups.Functors.ComplexLowerTruncation
import OAI.Topology.ArtinGroups.Complexes.ColorReduction
import OAI.Topology.ArtinGroups.Geometry.SphericalChamberConvexHull
import OAI.Topology.ArtinGroups.Harmonic.FusionIntegralCartan
import OAI.Topology.ArtinGroups.Harmonic.IntegralRowReflectApply
import OAI.Topology.ArtinGroups.Realizations.WeightChainCover
import OAI.Topology.ArtinGroups.Complexes.Cone
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistUnshiftedLayer
import OAI.Topology.ArtinGroups.Realizations.WeightedCounts
import OAI.Topology.ArtinGroups.Harmonic.Stage
import OAI.Topology.ArtinGroups.Harmonic.Contradiction
import OAI.Topology.ArtinGroups.Complexes.ProbeOrbitLevelDual
import OAI.Topology.ArtinGroups.Harmonic.ProbeActionTotalHom
import OAI.Topology.ArtinGroups.Functors.OrbitHomZeroAbove
import OAI.Topology.ArtinGroups.Complexes.ProbeOrbitGeneratorExterior
import OAI.Topology.ArtinGroups.Harmonic.SphericalPositiveCommonMultiple
import OAI.Topology.ArtinGroups.Harmonic.PositiveGradientStep
import OAI.Topology.ArtinGroups.Realizations.LiftedWeightStar
import OAI.Topology.ArtinGroups.Realizations.CellIndexTypeInjective
import OAI.Topology.ArtinGroups.Coxeter.VertexCoxeterFace
import OAI.Topology.ArtinGroups.Geometry.FiniteSetCenter
import OAI.Topology.ArtinGroups.Realizations.SalvettiProjection

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u} [Finite S] (M : CoxeterMatrix S)

theorem standard_salvetti_universal_cover_contractible :
    letI : Fintype S := Fintype.ofFinite S
    letI : DecidableEq S := Classical.decEq S
    IsCoveringMap (sourceSalvettiProjection M) ∧
    Function.Surjective (sourceSalvettiProjection M) ∧
    SimplyConnectedSpace (SalvettiCover M) ∧
    ContractibleSpace (SalvettiCover M) := by
  let : Fintype S := Fintype.ofFinite S
  let : DecidableEq S := Classical.decEq S
  exact sourceSalvettiProjection_universal M

end HarmonicArtin

end OAI
