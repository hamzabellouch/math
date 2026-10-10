import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CandidateBlockNonpos
import OAI.Topology.ArtinGroups.Complexes.ProbeFixedNoDiagonal
import OAI.Topology.ArtinGroups.Complexes.GeneratorArrayZeroLevel

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=K)

theorem sourceProbe_fixed_of_diagonal (T:Set S) (g:Artin M) (hg:g∈artinParabolic M T)
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool)
    (hz:∀l,classLevelArray R (bw g (initialClass R (.inr (α,b)))) (.inl α,l)=0) :
    bw g (initialClass R (.inr (α,b)))=initialClass R (.inr (α,b)) := by
  apply probeClass_fixed_of_no_diagonal Q
  · intro n u
    exact classGeneratorArray_zero_of_level R _ ⟨.inl α,n,u⟩ (hz (n+u))
  · intro n u
    rw [sourceProbeAction_exterior M T g hg _ _ (by intros; exact Sum.inl_ne_inr),
      sourceProbeInitial_array M]
    simp only [GeneratorPlacement.mk.injEq,true_and]
  · rw [sourceProbeAction_homDimension]
    exact initial_homDimension_le_one R
      (probeQuiver_no_loops Q (fusionQuiver_no_loops m d (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)))
      (.inr (α,b)) 0 0

theorem sourceCandidate_fixed_probes (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀L b,
      sourceProbeAction M (K:=ℂ) h (initialClass R (.inr ((.inl s,L),b)))=
        initialClass R (.inr ((.inl s,L),b)) := by
  obtain ⟨he,hj,hz⟩:=sourceCandidate_zero_block M T J J' hT z h hh q p p' X Y
  refine ⟨he,hj,?_⟩
  intro s hs hsJ L b
  exact sourceProbe_fixed_of_diagonal M T h hh (.inl s,L) b (hz s hs hsJ s hs hsJ L L b)

end HarmonicArtin

end OAI
