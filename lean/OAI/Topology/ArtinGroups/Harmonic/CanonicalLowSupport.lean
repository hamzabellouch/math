import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedFullWordMem
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionMultiplicity

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "C" => canonicalFusionLow m d hd hdiag (K:=ℂ)
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

lemma sourceCanonicalLow_support (J:Set S) (u:List J) (z:List ((S⊕Unit)×Bool))
    (s:S⊕Unit) (q:ℤ) (L:FusionLabel m) :
    ClassColorSupport Q (Set.range (unfoldedInclusion M J))
      (C (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) q (classLayer Q q (O z s L))) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalWordLow_colorSupport Q _ _ _ q (unfolded_full_word_mem M J u)
    (classLayer_lowerBound Q _ q)

lemma sourceCanonicalMultiplicity_support (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ) :
    ∀ v,v∉Sum.inl '' J→σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q v=0 := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := fun L=>
    sourceCanonicalLow_pure M J hJ u hu q _ (classLayer_lowerBound Q _ q) (classLayer_upperBound Q _ q)
  have hv:=canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  intro v hnot
  let H:FusionLabel m:=fun e=>⟨0,by have h:2 ≤ m e:=le_trans (by norm_num) (fusionLabelSize_ge_four M e);omega⟩
  have hz:∀ L,classTotalVector Q (C w q (classLayer Q q (O z s L))) (v,H)=0 := by
    intro L
    apply generatorVector_eq_zero_off Q _ (Set.range (unfoldedInclusion M J))
      (sourceCanonicalLow_support M J u z s q L)
    rintro ⟨⟨j,H'⟩,hh⟩
    have he:Sum.inl (j:S)=v:=congrArg Prod.fst hh
    exact hnot ⟨j,j.property,he⟩
  have hval:=congrFun hv (v,H)
  simp only [Finset.sum_apply,Pi.smul_apply,hz,smul_zero,Finset.sum_const_zero,fusionFold] at hval
  exact (mul_eq_zero.mp hval.symm).resolve_left (ne_of_gt (fusionWeight_pos m hm H))

end HarmonicArtin

end OAI
