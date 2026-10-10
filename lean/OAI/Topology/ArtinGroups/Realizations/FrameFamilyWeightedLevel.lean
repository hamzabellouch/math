import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma sourceFrameFamily_weighted_level (z:Artin M) (q:ℤ)
    (α:FusionVertex (V:=S⊕Unit) m) :
    (∑H,fusionWeight m H*(classLevelArray Q (sourceFrameFamily M z H) (α,q):ℝ))=
      fusionWeight m α.2*sourceMultiplicity M z q α.1 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M z
  rw [sourceMultiplicity_word,sourceFrameFamily_word]
  have h:=congrFun (fusionOrbitWeightedVector_eq m d hd hdiag hm (sourcePacketWord w) (.inr ()) q) α
  simpa only [fusionOrbitWeightedVector,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    fusionOrbitLayer_generator,fusionFold,sourcePacketMultiplicity] using h

end HarmonicArtin

end OAI
