import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueSingleOpen
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueActive
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCandidate
import OAI.Topology.ArtinGroups.Harmonic.ResidueActiveEmpty
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueSingleOpen
import OAI.Topology.ArtinGroups.Harmonic.ResidueActive

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidue_pointed_active_empty {P X:Deligne M} {q:ℤ} (hx:X≤P)
    (hh:pointedResidueHeight M f P X q<0)
    (hu:¬Nonempty (PointedResidueEarlierUpper M f P X q)) :
    pointedResidueActive M f P X q=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  apply hu
  exact ⟨pointedResidueUpperTop M f P X q hx,pointedResidueUpperTop_mem M f hx hh ⟨i,hi⟩⟩

lemma pointedResidue_pointed_candidate {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hh:pointedResidueHeight M f P X q<0)
    (hu:¬Nonempty (PointedResidueEarlierUpper M f P X q))
    (hl:¬Nonempty (PointedResidue M f true X q)) :
    PointedCandidate M f P.val.1 X.val.1 (sourceCosetRepresentative M X) q := by
  have ha:=pointedResidue_pointed_active_empty M f hX.1.le hh hu
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  refine ⟨deligne_lt_type M hX.1,?_,?_,?_⟩
  · have he:=pointedResidue_exterior_cap M f hX x z hx hz (closedNeighborhood Q (U P.val.1))
      (by simpa only [←unfoldedInclusion_range] using hboundary)
    simpa only [←unfoldedInclusion_range] using he
  · intro i hi hn
    change (framedCartan M *ᵥ pointedCosetVector M f X q) (.inl i)<0
    by_contra hr
    have hm:i∈pointedResidueActive M f P X q:=⟨hi,hn,le_of_not_gt hr⟩
    rw [ha] at hm
    exact hm
  · intro y hy hcap j
    have hy':y∈X.val.2:=by rw [sourceCosetRepresentative_spec];exact hy
    change pointedCosetVector M f X q (.inl (j:S))≤ pointedMultiplicity M f y q (.inl (j:S))
    by_contra hn
    apply hl
    apply pointedResidue_single_open M f X y hy' q j j.property
    · intro k hk
      exact pointedMultiplicity_cap_zero M f P.val.1 y q k hk hcap j (hX.1.le.1 j.property)
    · exact lt_of_not_ge hn

theorem pointedResidue_negative_pointeds_unique {strict:Bool} {P X Y:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (hY:PointedResidueAllowed M f strict P Y q)
    (x:Artin M) (hx:x∈P.val.2)
    (hboundary:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hhX:pointedResidueHeight M f P X q<0) (hhY:pointedResidueHeight M f P Y q<0)
    (huX:¬Nonempty (PointedResidueEarlierUpper M f P X q))
    (huY:¬Nonempty (PointedResidueEarlierUpper M f P Y q))
    (hlX:¬Nonempty (PointedResidue M f true X q))
    (hlY:¬Nonempty (PointedResidue M f true Y q)) : X=Y := by
  let z:=sourceCosetRepresentative M X
  let w:=sourceCosetRepresentative M Y
  let g:=w*z⁻¹
  have hz:z∈P.val.2:=hX.1.le.2 (sourceCosetRepresentative_mem M X)
  have hw:w∈P.val.2:=hY.1.le.2 (sourceCosetRepresentative_mem M Y)
  have hg:g∈artinParabolic M P.val.1:=by
    rw [←sourceCoset_eq M P z hz] at hw
    exact hw
  have he:g*z=w:=by dsimp [g];group
  have hcX:=pointedResidue_pointed_candidate M f hX x hx hboundary hhX huX hlX
  have hcY:=pointedResidue_pointed_candidate M f hY x hx hboundary hhY huY hlY
  obtain ⟨ht,hc⟩:=pointedCandidate_unique M f P.val.1 X.val.1 Y.val.1 P.property.1 z g hg q hcX
    (by simpa only [he] using hcY)
  apply Subtype.ext
  apply Prod.ext ht
  rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec]
  simpa only [he] using hc

end HarmonicArtin.ParabolicIntersections

end OAI
