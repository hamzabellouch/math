import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedMultiplicityZero
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed
import OAI.Topology.ArtinGroups.Harmonic.MultiplicityZero

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedCoset_exterior_cap (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀α∈U,α.1∉Sum.inl '' P.val.1) (q:ℤ)
    (h:∀H,ClassCapOn Q (pointedFamily M f x H) U q) :
    ∀H,ClassCapOn Q (pointedFamily M f z H) U q := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  intro H
  rw [he,pointedFamily_mul]
  exact sourceArtinAction_cap_exterior M P.val.1 _ hg _ U hU q (h H)

lemma pointedCoset_exterior_multiplicity (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    pointedMultiplicity M f z q v=pointedMultiplicity M f x q v := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  rw [he]
  exact pointedMultiplicity_exterior_ordered M f P.val.1 _ hg x v hv q

lemma pointedCosetVector_open_at (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    pointedCosetVector M f P q v=pointedMultiplicity M f z q v := by
  rw [pointedCosetVector_eq M f P z hz q]
  exact pointedHarmonicAt_outside M f P.val.1 z q v hv

lemma pointedResidue_exterior_cap {strict:Bool} {P X:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P X q) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H) (U\fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (pointedFamily M f z H) (U\fusionColorRegion m (Sum.inl '' X.val.1)) q := by
  have hout:=pointedCoset_exterior_cap M f P x z hx (h.1.le.2 hz)
    (U\fusionColorRegion m (Sum.inl '' P.val.1)) (fun α hα=>hα.2) q hE
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  by_cases hp:α.1∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,hei⟩:=hp
    have hxi:i∉X.val.1:=fun hh=>hα.2 ⟨i,hh,hei⟩
    have hzero:= (h.2 i hi hxi).1 k hk
    rw [pointedCosetVector_open_at M f X z hz _ (by
      rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))] at hzero
    change classLevelArray Q (pointedFamily M f z H) ((α.1,α.2),k)=0
    rw [←hei]
    exact (pointedMultiplicity_zero_iff M f z k _).mp hzero H α.2
  · exact (classCapOn_iff_level_zero Q _ _ _).mp (hout H) α ⟨hα.1,hp⟩ k hk

omit [Fintype S] [LinearOrder S] in
/-- Frame avoidance persists throughout a coset whose type avoids the frame. -/
lemma pointedCoset_avoids_frame (P : Deligne M) (x z : Artin M)
    (hx : x ∈ P.val.2) (hz : z ∈ P.val.2) (I : Set S)
    (hPI : P.val.1 ⊆ I) (hf : f ∉ I) (hxA : x ∈ artinParabolic M {f}ᶜ) :
    z ∈ artinParabolic M {f}ᶜ := by
  have hg : z*x⁻¹ ∈ artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have hsub : P.val.1 ⊆ {f}ᶜ := by
    intro i hi he
    exact hf (he ▸ hPI hi)
  have hm := (artinParabolic M {f}ᶜ).mul_mem (artinParabolic_mono M hsub hg) hxA
  simpa only [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one] using hm

end HarmonicArtin.ParabolicIntersections

end OAI
