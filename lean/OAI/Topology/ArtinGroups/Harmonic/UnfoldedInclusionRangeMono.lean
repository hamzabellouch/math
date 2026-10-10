import Mathlib
import OAI.Topology.ArtinGroups.Realizations.FrameFamilyWeightedLevel

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)

omit [Fintype S] in
lemma unfoldedInclusion_range_mono {J T:Set S} (h:J⊆T) :
    Set.range (unfoldedInclusion M J)⊆Set.range (unfoldedInclusion M T) := by
  rintro α ⟨⟨j,L⟩,rfl⟩
  exact ⟨(⟨j,h j.property⟩,L),rfl⟩

lemma source_cap_closed_mono {J T:Set S} (h:J⊆T) (z:Artin M) (q:ℤ)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q := by
  intro H i hi
  exact hz H i (closedNeighborhood_mono Q (unfoldedInclusion_range_mono M h) hi)

lemma source_cap_closed_extend (T J:Set S) (h:J⊆T)
    (z a:Artin M) (ha:a∈artinParabolic M J) (q:ℤ)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q)
    (hza:∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M T))) q := by
  intro H
  rw [unfoldedInclusion_range]
  apply source_cap_closed_of_cap_parts M T J h _ q (hza H)
  rw [sourceFrameFamily_mul]
  apply sourceArtinAction_cap_exterior M J a ha _ _ (fun α hα=>hα.2) q
  intro i hi
  apply hz H i
  rw [unfoldedInclusion_range]
  exact hi.1

lemma sourceMultiplicity_cap_zero (T:Set S) (z:Artin M) (q k:ℤ) (hq:q<k)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (Set.range (unfoldedInclusion M T)) q) (s:S) (hs:s∈T) :
    sourceMultiplicity M z k (.inl s)=0 := by
  let L:=fusionZeroLabel m (fusionLabelSize_ge_two M)
  have hw:=sourceFrameFamily_weighted_level M z k (.inl s,L)
  have he: (∑H,fusionWeight m H*
      (classLevelArray Q (sourceFrameFamily M z H) ((.inl s,L),k):ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro H _
    rw [(classCapOn_iff_level_zero Q _ _ _).mp (hz H) _ ⟨(⟨s,hs⟩,L),rfl⟩ k hq]
    simp
  rw [he] at hw
  exact (mul_eq_zero.mp hw.symm).resolve_left (ne_of_gt (fusionWeight_pos m (fusionLabelSize_ge_two M) L))

end HarmonicArtin

end OAI
