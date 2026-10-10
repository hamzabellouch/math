import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetGeometry
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedNullPatch
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueHeightZeroVector
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetVectorNullPatch
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma pointedResidueHeight_zero_vector {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hx:PointedResidueAllowed M f strict P X q) (hh:pointedResidueHeight M f P X q=0) :
    pointedCosetVector M f X q=pointedCosetVector M f P q := by
  have hn:=pointedResidueAllowed_le M f hx
  funext v
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hz:pointedCosetVector M f X q (.inl i)-pointedCosetVector M f P q (.inl i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _=>sub_nonpos.mpr (hn (.inl j)))).mp hh i (Set.mem_toFinset.mpr hi)
    exact sub_eq_zero.mp hz
  · exact (pointedCosetVector_upper_outside M f hx.1.le q v hp).symm

lemma pointedResidueAllowed_closed_trans {P X Y:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f false P X q) (hY:PointedResidueAllowed M f false X Y q) :
    PointedResidueAllowed M f false P Y q := by
  refine ⟨hY.1.trans hX.1,?_⟩
  intro i hi hni
  by_cases hxi:i∈X.val.1
  · have hv:=pointedResidueAllowed_le M f hX (.inl i)
    exact ⟨(hY.2 i hxi hni).1,(hY.2 i hxi hni).2.trans hv⟩
  · have he(k:ℤ):pointedCosetVector M f Y k (.inl i)=pointedCosetVector M f X k (.inl i):=
      (pointedCosetVector_upper_outside M f hY.1.le k _ (by
        rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))).symm
    simpa only [he] using hX.2 i hi hxi

lemma pointedResidue_zero_lower_iff {P X Y:Deligne M} {q:ℤ}
    (hx:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0) (hy:Y<X) :
    PointedResidueAllowed M f false P Y q ↔ PointedResidueAllowed M f false X Y q := by
  constructor
  · intro hY
    refine ⟨hy,?_⟩
    intro i hi hni
    rw [pointedResidueHeight_zero_vector M f hx hh]
    exact hY.2 i (hx.1.le.1 hi) hni
  · exact pointedResidueAllowed_closed_trans M f hx

lemma pointedResidue_zero_exterior {P X:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0)
    (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2) (I:Set S) (hPI:P.val.1⊆I)
    (c:S⊕Unit→ℝ) (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) :
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' X.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f z q v=c v := by
  intro v hv
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hn:(Sum.inl i:S⊕Unit)∉Sum.inl '' X.val.1:=by
      rcases hv with hv|hv
      · exact hv.2
      · exact False.elim (hv.1 ⟨i,hPI hi,rfl⟩)
    rw [←pointedCosetVector_open_at M f X z hz _ hn q,pointedResidueHeight_zero_vector M f h hh]
    exact pointedCosetVector_of_null_patch M f P x hx I hPI q c hcNull hdata i hi
  · rw [pointedCoset_exterior_multiplicity M f P x z hx (h.1.le.2 hz) v hp q]
    apply hdata v
    rcases hv with hv|hv
    · exact Or.inl ⟨hv.1,hp⟩
    · exact Or.inr hv

theorem pointedResidue_zero_ne_lower (P X:Deligne M) (x:Artin M) (hx:x∈P.val.2) (hxA:x∈artinParabolic M {f}ᶜ)
    (I:Set S) (hI:I.Nonempty) (hf:f∉I) (hPI:P.val.1⊆I) (q:ℤ)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v)
    (hX:PointedResidueAllowed M f false P X q) (hh:pointedResidueHeight M f P X q=0) :
    ∃Y:Deligne M,Y<X ∧ PointedResidueAllowed M f false P Y q := by
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  have hE':=pointedResidue_exterior_cap M f hX x z hx hz _ hE
  have hdata':=pointedResidue_zero_exterior M f hX hh x z hx hz I hPI c hcNull hdata
  obtain ⟨residue⟩:=pointedClosedResidue_nonempty M f X z hz
    (pointedCoset_avoids_frame M f P x z hx (hX.1.le.2 hz) I hPI hf hxA) I hI hf (hX.1.le.1.trans hPI)
    q c hc hcSupp hcPos hcNull hE' hdata'
  exact ⟨residue.val,residue.property.1,pointedResidueAllowed_closed_trans M f hX residue.property⟩

end HarmonicArtin.ParabolicIntersections

end OAI
