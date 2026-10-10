import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionZeroLabel
import OAI.Topology.ArtinGroups.Harmonic.SignedLetter
import OAI.Topology.ArtinGroups.Complexes.LevelArrayMinimalApply

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "aw" => sourceArtinAction M (K:=ℂ)

omit [Fintype S] in
lemma unfoldedInclusion_range (J:Set S) :
    Set.range (unfoldedInclusion M J)=fusionColorRegion m (Sum.inl '' J) := by
  ext α
  rcases α with ⟨v,L⟩
  constructor
  · rintro ⟨⟨j,H⟩,he⟩
    change (Sum.inl (j:S),H)=(v,L) at he
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
    exact ⟨j,j.property,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨(⟨j,hj⟩,L),rfl⟩

lemma closedNeighborhood_mono {V A:Type} (R:ReversibleQuiver V A)
    {U T:Set V} (h:U⊆T) : R.closedNeighborhood U⊆R.closedNeighborhood T := by
  rintro α (hα|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl (h hα)
  · exact Or.inr ⟨β,h hβ,a,hs,ht⟩

lemma sourceArtinAction_level_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (v:S⊕Unit) (hv:v∉Sum.inl '' J)
    (L:FusionLabel m) (k:ℤ) :
    classLevelArray Q (aw g x) ((v,L),k)=classLevelArray Q x ((v,L),k) := by
  obtain ⟨w,hw,rfl⟩:=artinParabolic_signed_word M J g hg
  rw [sourceArtinAction_signedWord]
  apply fusionWord_level_exterior m d hd hdiag
  intro b hb he
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
  exact hv ⟨a.1,hw a ha,he⟩

lemma sourceArtinAction_cap_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hU:∀ α∈U,α.1∉Sum.inl '' J) (q:ℤ) (hx:ClassCapOn Q x U q) :
    ClassCapOn Q (aw g x) U q := by
  apply classCapOn_of_level_eq Q U q _ hx
  intro α hα k
  exact sourceArtinAction_level_exterior M J g hg x α.1 (hU α hα) α.2 k

lemma sourceArtinAction_multiplicity_exterior (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J)
    (x:FusionLabel m→FiniteHomotopyClass Q (K:=ℂ)) (v:S⊕Unit) (hv:v∉Sum.inl '' J) (k:ℤ) :
    fusionFamilyMultiplicity m d hd hm (fun L=>aw g (x L)) k v=
      fusionFamilyMultiplicity m d hd hm x k v := by
  unfold fusionFamilyMultiplicity
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  congr 1
  simp only [classTotalVector_layer_apply]
  congr 1
  exact sourceArtinAction_level_exterior M J g hg (x L) v hv _ k

lemma source_cap_closed_of_cap_parts (I J:Set S) (_ : J⊆I)
    (x:FiniteHomotopyClass Q (K:=ℂ)) (q:ℤ)
    (hJ:ClassCapOn Q x (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hE:ClassCapOn Q x (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
      fusionColorRegion m (Sum.inl '' J)) q) :
    ClassCapOn Q x (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I))) q := by
  intro i hi
  by_contra hout
  apply hout
  apply hE i
  refine ⟨hi,?_⟩
  intro hj
  apply hout
  apply hJ i
  apply Or.inl
  rwa [unfoldedInclusion_range]

end HarmonicArtin

end OAI
