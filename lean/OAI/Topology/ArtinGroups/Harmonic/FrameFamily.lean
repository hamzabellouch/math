import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusionRange

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
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "aw" => sourceArtinAction M (K:=ℂ)

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_univ : artinParabolic M Set.univ=⊤ := by
  change Subgroup.closure ((generator M) '' Set.univ)=⊤
  rw [Set.image_univ]
  exact PresentedGroup.closure_range_of (braidRelators M)

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_surjective : Function.Surjective (sourceSignedWord M) := by
  intro x
  have hx:x∈artinParabolic M Set.univ := by rw [artinParabolic_univ]; trivial
  obtain ⟨w,_,hw⟩:=artinParabolic_signed_word M Set.univ x hx
  exact ⟨w,hw⟩

noncomputable def sourceFrameFamily (x:Artin M) (L:FusionLabel m) :
    FiniteHomotopyClass Q (K:=ℂ) := aw x (O [] (.inr ()) L)

lemma sourceFrameFamily_word (w:List (S×Bool)) :
    sourceFrameFamily M (sourceSignedWord M w)=O (sourcePacketWord w) (.inr ()) := by
  funext L
  rw [sourceFrameFamily,sourceArtinAction_signedWord]
  rfl

lemma sourceFrameFamily_mul (g x:Artin M) (L:FusionLabel m) :
    sourceFrameFamily M (g*x) L=aw g (sourceFrameFamily M x L) := by
  simp only [sourceFrameFamily,map_mul,Equiv.Perm.mul_apply]

noncomputable def sourceMultiplicity (x:Artin M) (k:ℤ) (v:S⊕Unit) : ℝ :=
  fusionFamilyMultiplicity m d hd hm (sourceFrameFamily M x) k v

lemma sourceMultiplicity_nonneg (x:Artin M) (k:ℤ) (v:S⊕Unit) :
    0 ≤ sourceMultiplicity M x k v := fusionFamilyMultiplicity_nonneg m d hd hm _ k v

lemma sourceMultiplicity_word (w:List (S×Bool)) (k:ℤ) :
    sourceMultiplicity M (sourceSignedWord M w) k=sourcePacketMultiplicity M w k := by
  unfold sourceMultiplicity
  rw [sourceFrameFamily_word,fusionFamilyMultiplicity_orbit]
  rfl

lemma sourceFrameFamily_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:Artin M) (v:S⊕Unit) (hv:v∉Sum.inl '' J) (L:FusionLabel m) (k:ℤ) :
    classLevelArray Q (sourceFrameFamily M (g*x) L) ((v,L),k)=
      classLevelArray Q (sourceFrameFamily M x L) ((v,L),k) := by
  rw [sourceFrameFamily_mul]
  exact sourceArtinAction_level_exterior M J g hg _ v hv L k

lemma sourceMultiplicity_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:Artin M) (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) :
    sourceMultiplicity M (g*x) k v=sourceMultiplicity M x k v := by
  unfold sourceMultiplicity
  have he:sourceFrameFamily M (g*x)=(fun L=>aw g (sourceFrameFamily M x L)):=
    funext (sourceFrameFamily_mul M g x)
  rw [he]
  exact sourceArtinAction_multiplicity_exterior M J g hg _ v hv k

lemma sourceMultiplicity_frame (x:Artin M) (k:ℤ) :
    sourceMultiplicity M x k (.inr ())=if k=0 then 1 else 0 := by
  obtain ⟨w,rfl⟩:=sourceSignedWord_surjective M x
  have hf:∀ a∈sourcePacketWord w,a.1≠(.inr () : S⊕Unit) := by
    intro a ha
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
    exact Sum.inl_ne_inr
  unfold sourceMultiplicity
  rw [sourceFrameFamily_word]
  unfold fusionFamilyMultiplicity
  simp_rw [classTotalVector_layer_apply,fusionOrbit_frame_level m d hd hdiag _ _ _ _ _ hf]
  by_cases hk:k=0
  · subst k
    simp only [and_true,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_ite,_root_.mul_one,MulZeroClass.mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact div_self (ne_of_gt (fusionWeight_pos m hm _))
  · simp only [hk,and_false,ite_false,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,zero_div]

end HarmonicArtin

end OAI
