import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily
import OAI.Topology.ArtinGroups.Complexes.FiniteFamilyLevelSupport
import OAI.Topology.ArtinGroups.Realizations.FiniteWeightedNatSums

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hm" => fusionLabelSize_ge_two M
local notation "Q" => fusionQuiver m d hd

lemma sourceMultiplicity_sum (x:Artin M) (k:ℤ) (v:S⊕Unit) :
    sourceMultiplicity M x k v=(∑ L,fusionWeight m L *
      (classLevelArray Q (sourceFrameFamily M x L) ((v,fusionZeroLabel m hm),k):ℝ)) /
      fusionWeight m (fusionZeroLabel m hm) := by
  unfold sourceMultiplicity fusionFamilyMultiplicity
  simp only [classTotalVector_layer_apply]

lemma sourceMultiplicity_values_finite (B:ℝ) :
    {r:ℝ | r≤B ∧ ∃ x k v,r=sourceMultiplicity M x k v}.Finite := by
  have h:=finite_normalized_weighted_nat_sums (fusionWeight m) (fusionWeight_pos m hm)
    (fusionWeight m (fusionZeroLabel m hm)) (fusionWeight_pos m hm _) B
  apply h.subset
  rintro r ⟨hr,x,k,v,rfl⟩
  exact ⟨hr,⟨fun L=>classLevelArray Q (sourceFrameFamily M x L)
    ((v,fusionZeroLabel m hm),k),sourceMultiplicity_sum M x k v⟩⟩

lemma sourceMultiplicity_support_finite (x:Artin M) :
    {k:ℤ | sourceMultiplicity M x k≠0}.Finite := by
  have h:=finiteFamily_level_support Q (sourceFrameFamily M x)
  apply h.subset
  intro k hk
  by_contra hn
  apply hk
  funext v
  have hz:∀ L,classLevelArray Q (sourceFrameFamily M x L)
      ((v,fusionZeroLabel m hm),k)=0 := by
    intro L
    by_contra hne
    exact hn ⟨L,_,hne⟩
  rw [sourceMultiplicity_sum]
  simp only [hz,Nat.cast_zero,MulZeroClass.mul_zero,Finset.sum_const_zero,zero_div,Pi.zero_apply]

end HarmonicArtin

end OAI
