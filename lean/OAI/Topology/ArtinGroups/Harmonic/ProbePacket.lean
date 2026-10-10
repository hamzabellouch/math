import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.ReducedWordProperty
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion
import OAI.Topology.ArtinGroups.Harmonic.SphericalPair
import OAI.Topology.ArtinGroups.Coxeter.AltListMap
import OAI.Topology.ArtinGroups.Coxeter.AlternatingLiftProd
import OAI.Topology.ArtinGroups.Quivers.ProbeSimpleEdge

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "f" => fun v=>classTwistPerm R (K:=K) (probeQuiver_no_loops Q hn) (Sum.inl v)

noncomputable def sourceProbePacket (s:S) : Equiv.Perm (FiniteHomotopyClass R (K:=K)) :=
  ((fusionExpandedWord (fusionLabelSize M) [Sum.inl s]).map f).prod

lemma sourceProbeWord_expand (u:List S) :
    (u.map (sourceProbePacket M (K:=K))).prod=
      ((fusionExpandedWord (fusionLabelSize M) (u.map Sum.inl)).map f).prod := by
  induction u with
  | nil=>rfl
  | cons s u ih=>
    simp only [List.map_cons,List.prod_cons,ih,sourceProbePacket,fusionExpandedWord,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.prod_append]

lemma spherical_probe_word_property (J:Set S) (hJ:IsSpherical M J)
    (u v:List J) (hu:(restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (hv:(restrictedMatrix M J).toCoxeterSystem.IsReduced v)
    (he:(restrictedMatrix M J).toCoxeterSystem.wordProd u=
      (restrictedMatrix M J).toCoxeterSystem.wordProd v) :
    ((u.map Subtype.val).map (sourceProbePacket M (K:=K))).prod=
      ((v.map Subtype.val).map (sourceProbePacket M (K:=K))).prod := by
  let g:=fun α:J×FusionLabel (fusionLabelSize M)=>f (unfoldedInclusion M J α)
  have hb:∀α β,((altList α β (unfoldedMatrix M J α β)).map g).prod=
      ((altList β α (unfoldedMatrix M J α β)).map g).prod:=by
    intro α β
    have hh:=probe_core_braid Q (K:=K) hn (unfoldedInclusion M J α) (unfoldedInclusion M J β)
    rw [unfolded_ordinaryMatrix M J hJ] at hh
    simp only [← altList_map,List.map_map,Function.comp_def] at hh
    simpa only [g] using hh
  have hh:=reduced_word_property (unfoldedMatrix M J).toCoxeterSystem g hb
    (fusionExpandedWord (fusionLabelSize M) u) (fusionExpandedWord (fusionLabelSize M) v)
    (unfolded_reducedWord M J hJ u hu) (unfolded_reducedWord M J hJ v hv)
    (unfolded_word_eq M J hJ u v he)
  rw [sourceProbeWord_expand,sourceProbeWord_expand]
  simp only [fusionExpandedWord_map,List.map_map,Function.comp_def,unfoldedInclusion,g] at hh ⊢
  convert hh using 1

lemma sourceProbePacket_braid (i j:S) :
    ((altList i j (M i j)).map (sourceProbePacket M (K:=K))).prod=
      ((altList j i (M i j)).map (sourceProbePacket M (K:=K))).prod := by
  by_cases hij:i=j
  · subst j; rfl
  by_cases hz:M i j=0
  · rw [hz]; rfl
  have hm:2≤M i j:=by have hh:=M.off_diagonal i j hij; omega
  let J:Set S:={i,j}
  let a:J:=⟨i,by simp [J]⟩
  let b:J:=⟨j,by simp [J]⟩
  have hab:a≠b:=fun h=>hij (congrArg Subtype.val h)
  have hJ:IsSpherical M J:=spherical_pair M i j hm
  have hu:=altList_reduced (restrictedMatrix M J).toCoxeterSystem a b hab (M i j)
    (Or.inr (by rfl : M i j≤restrictedMatrix M J a b))
  have hv:=altList_reduced (restrictedMatrix M J).toCoxeterSystem b a hab.symm (M i j)
    (Or.inr (by simpa only [restrictedMatrix_apply,a,b,M.symmetric j i] using (le_refl (M i j))))
  have he:=altList_braid (restrictedMatrix M J).toCoxeterSystem a b
  have hh:=spherical_probe_word_property M (K:=K) J hJ
    (altList a b (M i j)) (altList b a (M i j)) hu hv he
  simp only [altList_map,a,b] at hh
  simpa only [← altList_map,List.map_map,Function.comp_def] using hh

lemma sourceProbePacket_relators : ∀r∈braidRelators M,
    FreeGroup.lift (sourceProbePacket M (K:=K)) r=1 := by
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv]
  apply mul_inv_eq_one.mpr
  rw [alternating_lift_prod,alternating_lift_prod]
  exact sourceProbePacket_braid M i j

noncomputable def sourceProbeAction : Artin M →* Equiv.Perm (FiniteHomotopyClass R (K:=K)) :=
  PresentedGroup.toGroup (sourceProbePacket_relators M)

lemma sourceProbeAction_generator (s:S) :
    sourceProbeAction M (K:=K) (generator M s)=sourceProbePacket M s :=
  PresentedGroup.toGroup.of _

end HarmonicArtin

end OAI
