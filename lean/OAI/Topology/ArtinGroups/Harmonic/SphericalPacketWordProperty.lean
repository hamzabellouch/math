import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.ReducedWordProperty
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion
import OAI.Topology.ArtinGroups.Coxeter.AltListMap
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryTwistBraid
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordPerm

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "P" => fusionWordPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

theorem spherical_packet_word_property (J : Set S) (hJ : IsSpherical M J)
    (u v : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv : (restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he : (restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    P ((u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)).map fun s => (s,true))=
      P ((v.map fun j : J => (Sum.inl (j:S) : S⊕Unit)).map fun s => (s,true)) := by
  let f := fun α : J × FusionLabel (fusionLabelSize M) => classTwistPerm Q (K:=K) hn
    (unfoldedInclusion M J α)
  have hb : ∀ α β,((altList α β (unfoldedMatrix M J α β)).map f).prod=
      ((altList β α (unfoldedMatrix M J α β)).map f).prod := by
    intro α β
    have hh := ordinaryTwist_braid Q (K:=K) hn (unfoldedInclusion M J α) (unfoldedInclusion M J β)
    rw [unfolded_ordinaryMatrix M J hJ] at hh
    simpa only [← altList_map,List.map_map,Function.comp_def,f] using hh
  have hh := reduced_word_property (unfoldedMatrix M J).toCoxeterSystem f hb
    (fusionExpandedWord (fusionLabelSize M) u) (fusionExpandedWord (fusionLabelSize M) v)
    (unfolded_reducedWord M J hJ u hu) (unfolded_reducedWord M J hJ v hv)
    (unfolded_word_eq M J hJ u v he)
  rw [← fusionExpandedWord_perm,← fusionExpandedWord_perm]
  simp only [fusionExpandedWord_map,List.map_map,Function.comp_def,unfoldedInclusion,f] at hh ⊢
  convert hh using 1 <;> congr 3

end HarmonicArtin

end OAI
