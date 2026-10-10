import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCandidateFixed
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWordLeft
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft
import OAI.Topology.ArtinGroups.Harmonic.InitialProbe
import OAI.Topology.ArtinGroups.Harmonic.ProbeFixedDiagonal

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q

theorem pointedCandidate_comparison_parabolic (T J J':Set S) (hT:IsSpherical M T)
    (z h:Artin M) (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ h∈artinParabolic M J := by
  obtain ⟨hp,hj,hfix⟩:=pointedCandidate_fixed_probes M f T J J' hT z h hh q p p' X Y
  exact ⟨hp,hj,sourceProbe_parabolic_detector M T J hT h hh hfix⟩

end HarmonicArtin.ParabolicIntersections

end OAI
