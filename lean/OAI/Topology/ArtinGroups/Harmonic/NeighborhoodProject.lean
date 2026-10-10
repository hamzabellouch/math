import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TypeComponent
import OAI.Topology.ArtinGroups.Harmonic.CartanCommutingZero

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceNeighborhood_project (I:Set (S⊕Unit)) :
    closedNeighborhood Q (fusionColorRegion m I) ⊆ fusionColorRegion m (sourceClosedRegion M I) := by
  rintro α (ha|⟨β,hβ,a,hs,ht⟩)
  · exact Or.inl ha
  · by_cases hα:α.1∈I
    · exact Or.inl hα
    · have hn:β.1≠α.1:=by intro he;exact hα (he ▸ hβ)
      have hC:fusionFoldedCartan m (coxeterFusionEdge M)=framedCartan M:=by
        convert fusionFoldedCartan_eq_framedCartan M using 1
        congr 1
        exact Subsingleton.elim _ _
      have hh:=fusion_arrow_color_cartan_neg m (coxeterFusionEdge M) (fusionLabelSize_ge_two M) a
        (fun he=>hn ((congrArg Prod.fst hs).symm.trans
          (he.trans (congrArg Prod.fst ht))))
      rw [hC] at hh
      have hh':framedCartan M β.1 α.1<0:=by
        simpa only [show a.1.1=β from hs,show a.1.2=α from ht] using hh
      exact Or.inr ⟨β.1,hβ,by rwa [framedCartan_symm]⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceBlock_boundary_outside (P:Deligne M) (B:Set S) (_hB:B⊆P.val.1)
    (hc:∀i∈B,∀j∈P.val.1\B,M i j=2) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (Sum.inl '' B)) (ho:v∉Sum.inl '' B) :
    v∉Sum.inl '' P.val.1 := by
  rcases hv with hv|⟨u,hu,huv⟩
  · exact (ho hv).elim
  · obtain ⟨i,hi,rfl⟩:=hu
    rintro ⟨j,hj,rfl⟩
    have hjB:j∉B:=fun h=>ho ⟨j,h,rfl⟩
    have hz:=sourceCartan_commuting_zero M i j (hc i hi j ⟨hj,hjB⟩)
    rw [framedCartan_symm,hz] at huv
    exact (lt_irrefl 0 huv)

lemma sourceBlock_boundary_cap (P:Deligne M) (B:Set S) (hB:B⊆P.val.1)
    (hc:∀i∈B,∀j∈P.val.1\B,M i j=2) (q:ℕ) (hq:∀i∈B,sourcePeak M P i=q)
    (x:Artin M) (hx:x∈P.val.2) :
    ∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M B))\Set.range (unfoldedInclusion M B)) q := by
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have ha:α∈closedNeighborhood Q (fusionColorRegion m (Sum.inl '' B)):=by
    simpa only [unfoldedInclusion_range] using hα.1
  have ho':α∉fusionColorRegion m (Sum.inl '' B):=by simpa only [unfoldedInclusion_range] using hα.2
  have ho:α.1∉Sum.inl '' B:=ho'
  have hv:=sourceNeighborhood_project M (Sum.inl '' B) ha
  have hout:=sourceBlock_boundary_outside M P B hB hc α.1 hv ho
  have hnb:∃i∈B,framedCartan M (.inl i) α.1<0:=by
    rcases hv with hv|⟨u,hu,huv⟩
    · exact (ho hv).elim
    · obtain ⟨i,hi,rfl⟩:=hu
      exact ⟨i,hi,by rwa [framedCartan_symm]⟩
  have he:(k.toNat:ℤ)=k:=Int.toNat_of_nonneg (by omega)
  have hz:=sourceBlock_above_boundary M P B hB q hq α.1 hnb k.toNat (by omega)
  rw [he,sourceCosetVector_open_at M P x hx α.1 hout] at hz
  exact (sourceMultiplicity_zero_iff M x k α.1).mp hz H α.2

end HarmonicArtin

end OAI
