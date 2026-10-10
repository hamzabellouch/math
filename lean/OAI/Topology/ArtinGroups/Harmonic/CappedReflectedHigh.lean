import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedFullWordMem
import OAI.Topology.ArtinGroups.Complexes.CanonicalLowReflectedHigh
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistModern

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem source_capped_reflected_high (J:Set S) (hJ:IsSpherical M J)
    (u:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hcap:ClassCapOn Q x (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q) :
    classTotalVector Q (classLayer Q q (inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))) x))=
    rowReflectWord (unfoldedCartan Q)
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))).reverse
      (classTotalVector Q (classLayer Q q x)-classTotalVector Q
        (C (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit)) q (classLayer Q q x))) := by
  let w:=fusionExpandedWord (fusionLabelSize M) (u.map fun j:J=>(Sum.inl (j:S):S⊕Unit))
  rw [inverseWord_capped_layer Q w x (Set.range (unfoldedInclusion M J)) q hcap
    (unfolded_full_word_mem M J u)]
  have lower : ClassLowerBound Q q (classLayer Q q x) :=
    classLowerBound_of_representative Q _ (fun index => le_of_eq index.property.symm)
  have upper : ClassUpperBound Q q (classLayer Q q x) :=
    classUpperBound_of_representative Q _ (fun index => le_of_eq index.property)
  have hp:=sourceCanonicalLow_pure M J hJ u hu q (classLayer Q q x)
    lower upper
  rw [sourceCanonicalLow_eq] at hp ⊢
  exact canonicalLow_reflected_high Q hn w q (classLayer Q q x)
    lower upper hp.1 hp.2

end HarmonicArtin

end OAI
