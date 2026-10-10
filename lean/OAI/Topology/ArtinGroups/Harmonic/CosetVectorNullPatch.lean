import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed
import OAI.Topology.ArtinGroups.Harmonic.FoldedCartan
import OAI.Topology.ArtinGroups.Harmonic.MultiplicityZero

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma sourceCosetVector_of_null_patch (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hPI:P.val.1⊆I) (q:ℤ) (c:S⊕Unit→ℝ)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v) (i:S) (hi:i∈P.val.1) :
    sourceCosetVector M P q (.inl i)=c (.inl i) := by
  let p:S⊕Unit→ℝ:=fun v=>if v∈Sum.inl '' P.val.1 then c v else sourceMultiplicity M x q v
  have hp:p=sourceHarmonicAt M P.val.1 x q := by
    apply harmonicExtension_unique _ _ (framed_spherical_posDef M _ P.property.1)
    · intro v hv
      exact ite_eq_right hv
    · intro j
      exact null_patch (framedCartan_symm M) (framedCartan_off M)
        (Sum.inl '' I) (Sum.inl '' P.val.1) (Set.image_mono hPI) c
        (sourceMultiplicity M x q) hcNull hdata j j.property
  rw [sourceCosetVector_eq M P x hx q,←hp]
  exact ite_eq_left ⟨i,hi,rfl⟩

theorem sourceClosedResidue_nonempty (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=c v) : Nonempty (SourceResidue M false P q) := by
  by_contra hempty
  apply sourceGroup_isolated_harmonic_layer M I P.val.1 hI hPI P.property.1 x q hq
    c hc hcSupp hcPos hcNull hE hdata
  intro g hg hcap j
  by_contra hn
  have hj:sourceMultiplicity M (g*x) q (.inl (j:S))≤c (.inl (j:S)):=le_of_not_gt hn
  let z:=g*x
  have hz:z∈P.val.2 := by
    rw [sourceCosetRepresentative_spec] at hx ⊢
    change (g*x)*(sourceCosetRepresentative M P)⁻¹∈artinParabolic M P.val.1
    rw [_root_.mul_assoc]
    exact Subgroup.mul_mem _ hg hx
  let T:=P.val.1\{(j:S)}
  have ht:T⊆P.val.1:=Set.sdiff_subset
  let R:=sourceCoset M T (source_spherical_mono M ht P.property.1) z
  have hr:R≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M ht z
  have hrlt:R<P := by
    apply lt_of_le_of_ne hr
    intro he
    have he':T=P.val.1:=congrArg (fun A:Deligne M=>A.val.1) he
    have hmem:(j:S)∈T:=by rw [he'];exact j.property
    exact hmem.2 rfl
  have hrz:z∈R.val.2:=rightCoset_self M T z
  have hvec(k:ℤ)(i:S)(hi:i∉T):sourceCosetVector M R k (.inl i)=sourceMultiplicity M z k (.inl i) := by
    rw [sourceCosetVector_eq M R z hrz k]
    exact sourceHarmonicAt_outside M T z k _ (by
      rintro ⟨a,ha,he⟩;exact hi ((Sum.inl_injective he) ▸ ha))
  apply hempty
  refine ⟨R,hrlt,?_⟩
  intro i hi hnT
  have hei:i=(j:S) := by
    by_contra hne
    exact hnT ⟨hi,hne⟩
  subst i
  refine ⟨?_,?_⟩
  · intro k hk
    rw [hvec k j hnT,sourceMultiplicity_zero_iff]
    intro H L
    exact (classCapOn_iff_level_zero Q _ _ _).mp (hcap H) ((.inl (j:S)),L)
      (mem_closedNeighborhood Q ⟨j,hPI j.property,rfl⟩) k hk
  · change sourceCosetVector M R q (.inl (j:S))≤ sourceCosetVector M P q (.inl (j:S))
    rw [hvec q j hnT,sourceCosetVector_of_null_patch M P x hx I hPI q c hcNull hdata j j.property]
    exact hj

lemma sourceResidue_empty_type {P:Deligne M} (hP:P.val.1=∅) (strict:Bool) (q:ℤ) :
    IsEmpty (SourceResidue M strict P q) := by
  refine ⟨fun R=>?_⟩
  have ht:=deligne_lt_type M R.property.1
  rw [hP] at ht
  exact ht.not_ge (Set.empty_subset _)

end HarmonicArtin

end OAI
