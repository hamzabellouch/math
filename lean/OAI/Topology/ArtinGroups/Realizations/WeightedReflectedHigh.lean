import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CappedReflectedHigh
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionMultiplicity
import OAI.Topology.ArtinGroups.Harmonic.NegativePrepend
import OAI.Topology.ArtinGroups.Harmonic.RowReflectWordReverse

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
local notation "μ" => fusionOrbitMultiplicity m d hd hdiag hm
local notation "σ" => canonicalFusionMultiplicity m d hd hdiag hm

theorem source_weighted_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (z:List ((S⊕Unit)×Bool)) (s:S⊕Unit) (q:ℤ)
    (hcap:∀ L,ClassCapOn Q (O z s L)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    μ (negativePrepend (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z) s q=
      rowReflectWord (fusionFoldedCartan m d) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)).reverse
        (μ z s q-σ (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) z s q) := by
  let w:=u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)
  let A:=fun L=>classTotalVector Q (classLayer Q q (O z s L))
  let B:=fun L=>classTotalVector Q (C w q (classLayer Q q (O z s L)))
  have hp:∀ L,ClassLowerBound Q q (C w q (classLayer Q q (O z s L))) ∧
      ClassUpperBound Q q (C w q (classLayer Q q (O z s L))) := by
    intro label
    exact sourceCanonicalLow_pure M J hJ u hu q _
      (classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm))
      (classUpperBound_of_representative Q _ (fun index => le_of_eq index.property))
  have hA:(∑ L,fusionWeight m L • A L)=fusionFold m (μ z s q) := by
    rw [← fusionOrbitWeightedVector_class,fusionOrbitWeightedVector_eq m d hd hdiag hm]
  have hB:(∑ L,fusionWeight m L • B L)=fusionFold m (σ w z s q) :=
    canonicalFusionMultiplicity_fold m d hd hdiag hm w z s q hp
  apply fusionFold_injective m hm
  calc
    fusionFold m (μ (negativePrepend w z) s q)=
        ∑ L,fusionWeight m L • classTotalVector Q
          (classLayer Q q (inverseWordAction Q (fusionExpandedWord m w) (O z s L))) := by
      rw [← fusionOrbitWeightedVector_eq m d hd hdiag hm,fusionOrbitWeightedVector_class]
      simp only [fusionPacketOrbit_negativePrepend]
      congr 3
      funext L
      congr 9
      exact Subsingleton.elim _ _
    _ = ∑ L,fusionWeight m L • rowReflectWord (unfoldedCartan Q)
        (fusionExpandedWord m w).reverse (A L-B L) := by
      apply Finset.sum_congr rfl
      intro L _
      congr 1
      exact source_capped_reflected_high M J hJ u hu q (O z s L) (hcap L)
    _ = rowReflectWord (unfoldedCartan Q) (fusionExpandedWord m w).reverse
        ((∑ L,fusionWeight m L • A L)-(∑ L,fusionWeight m L • B L)) := by
      rw [← Finset.sum_sub_distrib,rowReflectWord_sum]
      apply Finset.sum_congr rfl
      intro L _
      rw [← smul_sub,rowReflectWord_smul]
    _ = fusionFold m (rowReflectWord (fusionFoldedCartan m d) w.reverse (μ z s q-σ w z s q)) := by
      rw [hA,hB,← fusionFold_sub,fusionQuiver_cartan]
      exact fusion_reverse_word_intertwining m hm d hdiag w _

end HarmonicArtin

end OAI
