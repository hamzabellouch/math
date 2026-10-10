import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SpecialResidueRank
import OAI.Topology.ArtinGroups.Harmonic.NullPatch2
import OAI.Topology.ArtinGroups.Harmonic.EligibleLeftNonempty

namespace OAI

namespace HarmonicArtin
open scoped _root_.Matrix _root_.OAI.Matrix
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceNegativeBlock_contractible (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (hs:sourceCosetSign M P (sourcePeak M P i) (.inl i)= -1)
    (V:SourceAllEligibleLower M P) (ho:i∉V.val.val.1) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  let B:=sourceTypeComponent M P i hi
  have hB:B⊆P.val.1:=sourceTypeComponent_subset M P i hi
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=sourceTypeComponent_commutes M P i hi
  let q:=sourcePeak M P i
  have hp:∀j∈B,sourcePeak M P j=q:=sourceTypeComponent_peak M P i hi
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  have hsg:∀j∈B,sourceCosetSign M P q (.inl j)=if true then -1 else 1:=by
    intro j hj
    exact (sourceTypeComponent_sign M P i hi j hj).trans hs
  let e:=sourceEligibleFactor M P R hB q true hp hsg (sourceBlock_vector M P B hB hc x hx q)
  have hn:=sourceBlock_eligible_nonempty M P B hB hc x hx V i (sourceTypeComponent_self M P i hi) ho
  have hr:ContractibleSpace (OrderWeights (SourceResidue M true R q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (sourceStrictResidue_contractible M R q x (rightCoset_self M B x)
        (sourceBlock_boundary_cap M P B hB hc q hp x hx) (Nonempty.map e hn))
  exact sourceBlock_allEligible_contractible M P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

lemma sourcePositiveBlock_contractible (P:Deligne M) (q:ℕ) (i:S) (_hi:i∈P.val.1)
    (hp:0<sourceCosetVector M P q (.inl i))
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q (.inl i)) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) (.inl i)}
  let B:=P.val.1∩I
  have hB:B⊆P.val.1:=Set.inter_subset_left
  have hiI:i∈I:=Relation.ReflTransGen.refl
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=by
    intro s hs t ht
    exact sourcePositiveBlock_commutes M P q (.inl i) hp s t hs.1 hs.2 ht.1
      (fun h=>ht.2 ⟨ht.1,h⟩)
  have hpeak:∀j∈B,sourcePeak M P j=q:=fun j hj=>sourceNullSign_peak M P q (.inl i) hp hn j hj.1 hj.2
  have hsg:∀j∈B,sourceCosetSign M P q (.inl j)=if false then -1 else 1:=fun j hj=>
    sourceNullSign_sign M P q (.inl i) hp hn (.inl j) hj.2
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  let c:=sourceNullPatch M P q (.inl i)
  have hI:Sum.inl '' I=sourcePositiveComponent M (sourceCosetVector M P q) (.inl i):=
    sourceNullSign_image M P q (.inl i) hn
  have hcSupp:∀v,v∉Sum.inl '' I→c v=0:=by
    intro v hv
    rw [hI] at hv
    exact ite_eq_right hv
  have hcPos:∀v,v∈Sum.inl '' I→0<c v:=by
    intro v hv
    rw [hI] at hv
    change 0<sourceNullPatch M P q (.inl i) v
    rw [sourceNullPatch,ite_eq_left hv]
    exact sourcePositiveComponent_positive M _ (.inl i) hp v hv
  have hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0:=by
    intro v hv
    rw [hI] at hv
    exact sourceNullPatch_row M P q (.inl i) hp hn v hv
  have hr:ContractibleSpace (OrderWeights (SourceResidue M false R q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (sourceSpecialResidue_contractible M R x (rightCoset_self M B x) I ⟨i,hiI⟩ Set.inter_subset_right
        q (by exact_mod_cast hn.1) c (sourceNullPatch_nonneg M P q (.inl i)) hcSupp hcPos hcNull
        (sourcePositive_block_cap M P q (.inl i) hp hn x hx)
        (sourcePositive_block_values M P q (.inl i) hp hn x hx))
  let e:=sourceEligibleFactor M P R hB q false hpeak hsg (sourceBlock_vector M P B hB hc x hx q)
  exact sourceBlock_allEligible_contractible M P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

theorem sourceAllEligibleLower_contractible (P:Deligne M) (hne:Nonempty (SourceAllEligibleLower M P)) :
    ContractibleSpace (OrderWeights (SourceAllEligibleLower M P)) := by
  obtain ⟨V⟩:=hne
  have hnot:¬P.val.1⊆V.val.val.1:=by
    intro h
    exact V.property.1.ne (deligne_eq_of_le_type_eq M V.property.1.le
      (Set.Subset.antisymm V.property.1.le.1 h))
  obtain ⟨i,hi,ho⟩:=Set.not_subset.mp hnot
  let q:=sourcePeak M P i
  by_cases hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q (.inl i)
  · exact sourcePositiveBlock_contractible M P q i hi (sourcePeak_positive M P i hi) hn
  · have hs:sourceCosetSign M P q (.inl i)= -1:=by
      change sourceSignAt M _ q (.inl i)= -1
      rw [sourceSignAt,ite_eq_right (ne_of_gt (sourcePeak_positive M P i hi)),ite_eq_right hn]
    exact sourceNegativeBlock_contractible M P i hi hs V ho

end HarmonicArtin

end OAI
