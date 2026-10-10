import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueSingleOpen
import OAI.Topology.ArtinGroups.Harmonic.ResidueActive

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidue_source_active_empty {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:sourceResidueHeight M P X q<0)
    (hu:¬Nonempty (SourceResidueEarlierUpper M P X q)) :
    sourceResidueActive M P X q=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  apply hu
  exact ⟨sourceResidueUpperTop M P X q hx,sourceResidueUpperTop_mem M hx hh ⟨i,hi⟩⟩

lemma sourceResidue_source_candidate {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hh:sourceResidueHeight M P X q<0)
    (hu:¬Nonempty (SourceResidueEarlierUpper M P X q))
    (hl:¬Nonempty (SourceResidue M true X q)) :
    SourceCandidate M P.val.1 X.val.1 (sourceCosetRepresentative M X) q := by
  have ha:=sourceResidue_source_active_empty M hX.1.le hh hu
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  refine ⟨deligne_lt_type M hX.1,?_,?_,?_⟩
  · have he:=sourceResidue_exterior_cap M hX x z hx hz (closedNeighborhood Q (U P.val.1))
      (by simpa only [←unfoldedInclusion_range] using hboundary)
    simpa only [←unfoldedInclusion_range] using he
  · intro i hi hn
    change (framedCartan M *ᵥ sourceCosetVector M X q) (.inl i)<0
    by_contra hr
    have hm:i∈sourceResidueActive M P X q:=⟨hi,hn,le_of_not_gt hr⟩
    rw [ha] at hm
    exact hm
  · intro y hy hcap j
    have hy':y∈X.val.2:=by rw [sourceCosetRepresentative_spec];exact hy
    change sourceCosetVector M X q (.inl (j:S))≤ sourceMultiplicity M y q (.inl (j:S))
    by_contra hn
    apply hl
    apply sourceResidue_single_open M X y hy' q j j.property
    · intro k hk
      exact sourceMultiplicity_cap_zero M P.val.1 y q k hk hcap j (hX.1.le.1 j.property)
    · exact lt_of_not_ge hn

theorem sourceResidue_negative_sources_unique {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) (hY:SourceResidueAllowed M strict P Y q)
    (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hhX:sourceResidueHeight M P X q<0) (hhY:sourceResidueHeight M P Y q<0)
    (huX:¬Nonempty (SourceResidueEarlierUpper M P X q))
    (huY:¬Nonempty (SourceResidueEarlierUpper M P Y q))
    (hlX:¬Nonempty (SourceResidue M true X q))
    (hlY:¬Nonempty (SourceResidue M true Y q)) : X=Y := by
  let z:=sourceCosetRepresentative M X
  let w:=sourceCosetRepresentative M Y
  let g:=w*z⁻¹
  have hz:z∈P.val.2:=hX.1.le.2 (sourceCosetRepresentative_mem M X)
  have hw:w∈P.val.2:=hY.1.le.2 (sourceCosetRepresentative_mem M Y)
  have hg:g∈artinParabolic M P.val.1:=by
    rw [←sourceCoset_eq M P z hz] at hw
    exact hw
  have he:g*z=w:=by dsimp [g];group
  have hcX:=sourceResidue_source_candidate M hX x hx hboundary hhX huX hlX
  have hcY:=sourceResidue_source_candidate M hY x hx hboundary hhY huY hlY
  obtain ⟨ht,hc⟩:=sourceCandidate_unique M P.val.1 X.val.1 Y.val.1 P.property.1 z g hg q hcX
    (by simpa only [he] using hcY)
  apply Subtype.ext
  apply Prod.ext ht
  rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec]
  simpa only [he] using hc

end HarmonicArtin

end OAI
