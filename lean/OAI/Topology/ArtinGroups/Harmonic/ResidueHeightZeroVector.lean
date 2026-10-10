import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetVectorNullPatch
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceResidueHeight_zero_vector {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hx:SourceResidueAllowed M strict P X q) (hh:sourceResidueHeight M P X q=0) :
    sourceCosetVector M X q=sourceCosetVector M P q := by
  have hn:=sourceResidueAllowed_le M hx
  funext v
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hz:sourceCosetVector M X q (.inl i)-sourceCosetVector M P q (.inl i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _=>sub_nonpos.mpr (hn (.inl j)))).mp hh i (Set.mem_toFinset.mpr hi)
    exact sub_eq_zero.mp hz
  · exact (sourceCosetVector_upper_outside M hx.1.le q v hp).symm

lemma sourceResidueAllowed_closed_trans {P X Y:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M false P X q) (hY:SourceResidueAllowed M false X Y q) :
    SourceResidueAllowed M false P Y q := by
  refine ⟨hY.1.trans hX.1,?_⟩
  intro i hi hni
  by_cases hxi:i∈X.val.1
  · have hv:=sourceResidueAllowed_le M hX (.inl i)
    exact ⟨(hY.2 i hxi hni).1,(hY.2 i hxi hni).2.trans hv⟩
  · have he(k:ℤ):sourceCosetVector M Y k (.inl i)=sourceCosetVector M X k (.inl i):=
      (sourceCosetVector_upper_outside M hY.1.le k _ (by
        rintro ⟨j,hj,hh⟩;exact hxi ((Sum.inl_injective hh) ▸ hj))).symm
    simpa only [he] using hX.2 i hi hxi

lemma sourceResidue_zero_lower_iff {P X Y:Deligne M} {q:ℤ}
    (hx:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0) (hy:Y<X) :
    SourceResidueAllowed M false P Y q ↔ SourceResidueAllowed M false X Y q := by
  constructor
  · intro hY
    refine ⟨hy,?_⟩
    intro i hi hni
    rw [sourceResidueHeight_zero_vector M hx hh]
    exact hY.2 i (hx.1.le.1 hi) hni
  · exact sourceResidueAllowed_closed_trans M hx

lemma sourceResidue_zero_exterior {P X:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0)
    (x z:Artin M) (hx:x∈P.val.2) (hz:z∈X.val.2) (I:Set S) (hPI:P.val.1⊆I)
    (c:S⊕Unit→ℝ) (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) :
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' X.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M z q v=c v := by
  intro v hv
  by_cases hp:v∈Sum.inl '' P.val.1
  · obtain ⟨i,hi,rfl⟩:=hp
    have hn:(Sum.inl i:S⊕Unit)∉Sum.inl '' X.val.1:=by
      rcases hv with hv|hv
      · exact hv.2
      · exact False.elim (hv.1 ⟨i,hPI hi,rfl⟩)
    rw [←sourceCosetVector_open_at M X z hz _ hn q,sourceResidueHeight_zero_vector M h hh]
    exact sourceCosetVector_of_null_patch M P x hx I hPI q c hcNull hdata i hi
  · rw [sourceCoset_exterior_multiplicity M P x z hx (h.1.le.2 hz) v hp q]
    apply hdata v
    rcases hv with hv|hv
    · exact Or.inl ⟨hv.1,hp⟩
    · exact Or.inr hv

theorem sourceResidue_zero_ne_lower (P X:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v)
    (hX:SourceResidueAllowed M false P X q) (hh:sourceResidueHeight M P X q=0) :
    ∃Y:Deligne M,Y<X ∧ SourceResidueAllowed M false P Y q := by
  let z:=sourceCosetRepresentative M X
  have hz:=sourceCosetRepresentative_mem M X
  have hE':=sourceResidue_exterior_cap M hX x z hx hz _ hE
  have hdata':=sourceResidue_zero_exterior M hX hh x z hx hz I hPI c hcNull hdata
  obtain ⟨residue⟩:=sourceClosedResidue_nonempty M X z hz I hI (hX.1.le.1.trans hPI)
    q hq c hc hcSupp hcPos hcNull hE' hdata'
  exact ⟨residue.val,residue.property.1,sourceResidueAllowed_closed_trans M hX residue.property⟩

end HarmonicArtin

end OAI
