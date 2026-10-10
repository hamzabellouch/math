import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.Harmonic.FrameFamilyTopProportional
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionProfilePositiveEvery
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

lemma pointedFamily_top_proportional (x:Artin M) (s:S⊕Unit) (q c:ℤ) :
    ∃ a:ℝ,0≤a ∧ ∀ L,(∑ H,fusionWeight m H*
      (classLayerTopDimension Q q (s,L) c (pointedFamily M f x H):ℝ))=a*fusionWeight m L := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  rw [pointedFamily_word]
  exact fusionPacketOrbit_top_proportional m d (coxeterFusionEdge_symm M)
    (coxeterFusionEdge_diag M) (fusionLabelSize_ge_two M) (sourcePacketWord w) (.inl f) s q c

lemma pointedFamily_top_zero_of_label (x:Artin M) (s:S⊕Unit) (q:ℤ)
    (L₀:FusionLabel m)
    (hz:∀ H c,classLayerTopDimension Q q (s,L₀) c (pointedFamily M f x H)=0) :
    ∀ H L c,classLayerTopDimension Q q (s,L) c (pointedFamily M f x H)=0 := by
  intro H L c
  apply Nat.eq_zero_of_not_pos
  intro hp
  obtain ⟨H',hp'⟩:=fusion_profile_positive_every_label m (fusionLabelSize_ge_two M)
    (fun H L=>classLayerTopDimension Q q (s,L) c (pointedFamily M f x H))
    (pointedFamily_top_proportional M f x s q c) hp L₀
  exact hp'.ne' (hz H' c)

end HarmonicArtin.ParabolicIntersections

end OAI
