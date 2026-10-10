import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeEligibleBlocks
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeNullBlockData
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedSpecialResidue

namespace OAI

/-! Contractibility of nonempty descending lower neighborhoods of the relative height. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped _root_.Matrix _root_.OAI.Matrix
open CategoryTheory Simplicial ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeNegativeBlock_contractible (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (hp:0<pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i))
    (hs:relativeSign M U (pointedProfile M f P cutoff) (relativePeak M f cutoff P i) (.inl i)= -1)
    (V:RelativeAllEligibleLower M f U cutoff P) (ho:i∉V.val.val.1) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let B:=sourceTypeComponent M P i hi
  have hB:B⊆P.val.1:=sourceTypeComponent_subset M P i hi
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=sourceTypeComponent_commutes M P i hi
  let q:=relativePeak M f cutoff P i
  have hpeak:∀j∈B,relativePeak M f cutoff P j=q:=pointedTypeComponent_peak M f cutoff P i hi
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  have hsg:∀j∈B,relativeSign M U (pointedProfile M f P cutoff) q (.inl j)=if true then -1 else 1:=by
    intro j hj
    exact (pointedTypeComponent_sign M f U cutoff P i hi q hp j hj).trans hs
  let e:=relativeEligibleFactor M f U cutoff P R hB q true hpeak hsg
    (pointedBlock_vector M f P B hB hc x hx (cutoff+q))
  have hn:=relativeBlock_eligible_nonempty M f U cutoff P B hB hc x hx V i
    (sourceTypeComponent_self M P i hi) ho
  have hr:ContractibleSpace (OrderWeights (PointedResidue M f true R (cutoff+q))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (pointedStrictResidue_contractible M f R (cutoff+q) x (rightCoset_self M B x)
        (pointedBlock_boundary_cap M f cutoff P B hB hc q hpeak x hx) (Nonempty.map e hn))
  exact relativeBlock_allEligible_contractible M f U cutoff P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

lemma relativePositiveBlock_contractible (P:Deligne M) (q:ℕ) (i:S)
    (hp:0<pointedProfile M f P cutoff q (.inl i))
    (hn:RelativeNullData M U (pointedProfile M f P cutoff) q (.inl i))
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (pointedProfile M f P cutoff q) (.inl i)}
  let B:=P.val.1∩I
  have hB:B⊆P.val.1:=Set.inter_subset_left
  have hiI:i∈I:=Relation.ReflTransGen.refl
  have hfI:f∉I:=fun h => hf (hn.1 h)
  have hc:∀s∈B,∀t∈P.val.1\B,M s t=2:=by
    intro s hs t ht
    exact pointedPositiveBlock_commutes M f cutoff P q (.inl i) hp s t hs.1 hs.2 ht.1
      (fun h=>ht.2 ⟨ht.1,h⟩)
  have hpeak:∀j∈B,relativePeak M f cutoff P j=q:=fun j hj=>
    relativeNullSign_peak M f U cutoff P q (.inl i) hp hn j hj.1 hj.2
  have hsg:∀j∈B,relativeSign M U (pointedProfile M f P cutoff) q (.inl j)=if false then -1 else 1:=
    fun j hj=>relativeNullSign_sign M f U cutoff P q (.inl i) hp hn (.inl j) hj.2
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  let R:=sourceCoset M B (source_spherical_mono M hB P.property.1) x
  let c:=relativeNullPatch M f cutoff P q (.inl i)
  have hI:Sum.inl '' I=sourcePositiveComponent M (pointedProfile M f P cutoff q) (.inl i):=
    relativeNullSign_image M f U cutoff P q (.inl i) hn hU
  have hcSupp:∀v,v∉Sum.inl '' I→c v=0:=by
    intro v hv
    rw [hI] at hv
    exact ite_eq_right hv
  have hcPos:∀v,v∈Sum.inl '' I→0<c v:=by
    intro v hv
    rw [hI] at hv
    change 0<relativeNullPatch M f cutoff P q (.inl i) v
    rw [relativeNullPatch,ite_eq_left hv]
    exact sourcePositiveComponent_positive M _ (.inl i) hp v hv
  have hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0:=by
    intro v hv
    rw [hI] at hv
    exact relativeNullPatch_row M f U cutoff P q (.inl i) hp hn v hv
  have hr:ContractibleSpace (OrderWeights (PointedResidue M f false R (cutoff+q))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (pointedSpecialResidue_contractible M f R x (rightCoset_self M B x) hxA I ⟨i,hiI⟩ hfI
        Set.inter_subset_right (cutoff+q) c (relativeNullPatch_nonneg M f cutoff P q (.inl i))
        hcSupp hcPos hcNull (relativePositive_block_cap M f U cutoff P q (.inl i) hp hn hU x hx)
        (relativePositive_block_values M f U cutoff P q (.inl i) hp hn hU x hx))
  let e:=relativeEligibleFactor M f U cutoff P R hB q false hpeak hsg
    (pointedBlock_vector M f P B hB hc x hx (cutoff+q))
  exact relativeBlock_allEligible_contractible M f U cutoff P B hB hc x hx
    ((weightHomeomorph e).contractibleSpace_iff.mpr hr)

/-- The lower-link argument uses no positivity assumption on invisible colors. -/
theorem relativeAllEligibleLower_contractible (P:Deligne M)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ)
    (hne:Nonempty (RelativeAllEligibleLower M f U cutoff P)) :
    ContractibleSpace (OrderWeights (RelativeAllEligibleLower M f U cutoff P)) := by
  obtain ⟨V⟩:=hne
  have hnot:¬P.val.1⊆V.val.val.1:=by
    intro h
    exact V.property.1.ne (deligne_eq_of_le_type_eq M V.property.1.le
      (Set.Subset.antisymm V.property.1.le.1 h))
  obtain ⟨i,hi,ho⟩:=Set.not_subset.mp hnot
  let q:=relativePeak M f cutoff P i
  have hp : 0 < pointedProfile M f P cutoff q (.inl i) :=
    relativeEligible_positive M f U cutoff (V.property.2 i hi ho)
  by_cases hn:relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) q (.inl i)
  · exact relativePositiveBlock_contractible M f U cutoff P q i hp
      (relativeNullData_of_positive M U _ q (.inl i) hp hn) hU hf hxA
  · have hs:relativeSign M U (pointedProfile M f P cutoff) q (.inl i)= -1:=by
      simp only [relativeSign,ne_of_gt hp,hn,↓reduceIte]
    exact relativeNegativeBlock_contractible M f U cutoff P i hi hp hs V ho

end HarmonicArtin.ParabolicIntersections

end OAI
