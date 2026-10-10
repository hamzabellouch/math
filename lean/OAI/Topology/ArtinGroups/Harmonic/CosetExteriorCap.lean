import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed
import OAI.Topology.ArtinGroups.Harmonic.MultiplicityZero

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceCoset_exterior_cap (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m)) (hU:∀α∈U,α.1∉Sum.inl '' P.val.1) (q:ℤ)
    (h:∀H,ClassCapOn Q (sourceFrameFamily M x H) U q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M z H) U q := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  intro H
  rw [he,sourceFrameFamily_mul]
  exact sourceArtinAction_cap_exterior M P.val.1 _ hg _ U hU q (h H)

lemma sourceCoset_exterior_multiplicity (P:Deligne M) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    sourceMultiplicity M z q v=sourceMultiplicity M x q v := by
  have hg:z*x⁻¹∈artinParabolic M P.val.1 := by
    rw [←sourceCoset_eq M P x hx] at hz
    exact hz
  have he:z=(z*x⁻¹)*x:=by group
  rw [he]
  exact sourceMultiplicity_exterior M P.val.1 _ hg x v hv q

lemma sourceCosetVector_open_at (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (v:S⊕Unit) (hv:v∉Sum.inl '' P.val.1) (q:ℤ) :
    sourceCosetVector M P q v=sourceMultiplicity M z q v := by
  rw [sourceCosetVector_eq M P z hz q]
  exact sourceHarmonicAt_outside M P.val.1 z q v hv

lemma sourceResidue_exterior_cap {strict:Bool} {P X:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P X q) (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2)
    (U:Set (FusionVertex (V:=S⊕Unit) m))
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H) (U\fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M z H) (U\fusionColorRegion m (Sum.inl '' X.val.1)) q := by
  have hout:=sourceCoset_exterior_cap M P x z hx (h.1.le.2 hz)
    (U\fusionColorRegion m (Sum.inl '' P.val.1)) (fun α hα=>hα.2) q hE
  intro H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  by_cases hp:α.1∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,hei⟩:=hp
    have hxi:i∉X.val.1:=fun hh=>hα.2 ⟨i,hh,hei⟩
    have hzero:= (h.2 i hi hxi).1 k hk
    rw [sourceCosetVector_open_at M X z hz _ (by
      rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))] at hzero
    change classLevelArray Q (sourceFrameFamily M z H) ((α.1,α.2),k)=0
    rw [←hei]
    exact (sourceMultiplicity_zero_iff M z k _).mp hzero H α.2
  · exact (classCapOn_iff_level_zero Q _ _ _).mp (hout H) α ⟨hα.1,hp⟩ k hk

end HarmonicArtin

end OAI
