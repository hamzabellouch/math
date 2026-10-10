import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCandidateBlock
import OAI.Topology.ArtinGroups.Harmonic.ProbeFixedDiagonal
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CandidateBlockNonpos
import OAI.Topology.ArtinGroups.Complexes.ProbeFixedNoDiagonal
import OAI.Topology.ArtinGroups.Complexes.GeneratorArrayZeroLevel

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

theorem pointedCandidate_fixed_probes (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:PointedCappedCandidate M f T J z q p) (Y:PointedCappedCandidate M f T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=ℂ) h (initialClass R (.inr ((.inl s,L),b)))=
        initialClass R (.inr ((.inl s,L),b)) := by
  obtain ⟨he,hj,hz⟩:=pointedCandidate_zero_block M f T J J' hT z h hh q p p' X Y
  refine ⟨he,hj,?_⟩
  intro s hs hsJ L b
  exact sourceProbe_fixed_of_diagonal M T h hh (.inl s,L) b (hz s hs hsJ s hs hsJ L L b)

end HarmonicArtin.ParabolicIntersections

end OAI
