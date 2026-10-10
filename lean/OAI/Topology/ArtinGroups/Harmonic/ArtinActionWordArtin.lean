import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ReducedExpression
import OAI.Topology.ArtinGroups.Harmonic.ArtinAction
import OAI.Topology.ArtinGroups.Complexes.InverseWordActionAppend
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistCapDisjoint

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "aw" => sourceArtinAction M (K:=K)

lemma sourceArtinAction_wordArtin (u:List S) :
    aw (wordArtin M u)=((fusionExpandedWord (fusionLabelSize M)
      (u.map (Sum.inl : S→S⊕Unit))).map (classTwistPerm Q (K:=K) hn)).prod := by
  have hh:=fusionExpandedWord_perm (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)
    (u.map (Sum.inl : S→S⊕Unit))
  rw [fusionWordPacketPerm_positive] at hh
  have ha: aw (wordArtin M u)=
      ((u.map (Sum.inl : S→S⊕Unit)).map
        (fusionPacketPerm (fusionLabelSize M) (coxeterFusionEdge M)
          (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M))).prod := by
    simp only [wordArtin,map_list_prod,List.map_map,sourceArtinAction_generator,Function.comp_def]
  refine ha.trans (hh.symm.trans ?_)
  exact congrArg (fun h : DecidableEq (FusionQuiverArrow (fusionLabelSize M) (coxeterFusionEdge M)) =>
    ((fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))).map
      (@classTwistPerm _ _ K Q _ _ _ _ h hn)).prod) (Subsingleton.elim _ _)

lemma sourceArtinAction_positiveWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u) x=positiveWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  rw [sourceArtinAction_wordArtin,positiveWordAction_eq_prod Q hn]

lemma sourceArtinAction_negativeWord (u:List S) (x:FiniteHomotopyClass Q (K:=K)) :
    aw (wordArtin M u)⁻¹ x=inverseWordAction Q
      (fusionExpandedWord (fusionLabelSize M) (u.map (Sum.inl : S→S⊕Unit))) x := by
  apply (aw (wordArtin M u)).injective
  rw [map_inv]
  change (aw (wordArtin M u)) ((aw (wordArtin M u)).symm x)=_
  rw [Equiv.apply_symm_apply,sourceArtinAction_positiveWord,positive_inverseWord Q hn]

theorem source_finiteFamily_cap_accessible {F:Type*} [Finite F]
    (J:Set S) (hJ:IsSpherical M J)
    (x:F→FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hb:∀ f,ClassCapOn Q (x f)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J)) \
        Set.range (unfoldedInclusion M J)) q) :
    ∃ g∈artinParabolic M J,∀ f,ClassCapOn Q (aw g (x f))
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q := by
  have : Finite (restrictedMatrix M J).Group:=restricted_finite M J hJ
  obtain ⟨z,hz⟩:=exists_longest (restrictedMatrix M J).toCoxeterSystem
  obtain ⟨u,hu,he⟩:=(restrictedMatrix M J).toCoxeterSystem.exists_isReduced z
  let w:=fusionExpandedWord (fusionLabelSize M) u
  have hw:(unfoldedMatrix M J).toCoxeterSystem.IsReduced w:=unfolded_reducedWord M J hJ u hu
  have hp:(unfoldedMatrix M J).toCoxeterSystem.wordProd w=unfoldedHom M J hJ z := by
    rw [he,unfoldedHom_wordProd]
  have hlong:∀ β,(unfoldedMatrix M J).toCoxeterSystem.length
      ((unfoldedMatrix M J).toCoxeterSystem.wordProd w*(unfoldedMatrix M J).toCoxeterSystem.simple β)+1=
      (unfoldedMatrix M J).toCoxeterSystem.length ((unfoldedMatrix M J).toCoxeterSystem.wordProd w) := by
    rw [hp]
    exact all_descents_of_longest (unfoldedMatrix M J).toCoxeterSystem _
      (unfolded_longest M J hJ z hz)
  have hdec:=longest_inverseWord_testUpper Q (K:=K) hn (unfoldedMatrix M J) (unfoldedInclusion M J)
    (unfolded_ordinaryMatrix M J hJ) w hw hlong
  obtain ⟨n,hcap⟩:=finiteFamily_cap_accessible_of_test_decrement Q
    (w.map (unfoldedInclusion M J)) (Set.range (unfoldedInclusion M J))
    (fun β hβ=>by obtain ⟨α,_,rfl⟩:=List.mem_map.mp hβ; exact ⟨α,rfl⟩) hdec x q hb
  let a:=wordArtin M (u.map Subtype.val)
  have ha:a∈artinParabolic M J := wordArtin_mem_parabolic M J _
    (by intro s hs; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hs; exact i.property)
  refine ⟨a⁻¹^n,(artinParabolic M J).pow_mem ((artinParabolic M J).inv_mem ha) n,fun f=>?_⟩
  have hact: (fun y : FiniteHomotopyClass Q (K:=K)=>aw a⁻¹ y)=
      inverseWordAction Q (w.map (unfoldedInclusion M J)) := by
    funext y
    rw [sourceArtinAction_negativeWord]
    congr 2
    simpa only [List.map_map,Function.comp_def,w,unfoldedInclusion] using
      fusionExpandedWord_map (fusionLabelSize M) (fun i : J=>(Sum.inl (i:S) : S⊕Unit)) u
  have hpow:aw (a⁻¹^n) (x f)= (inverseWordAction Q (w.map (unfoldedInclusion M J)))^[n] (x f) := by
    rw [map_pow]
    change ((aw a⁻¹)^n) (x f)=_
    rw [Equiv.Perm.coe_pow]
    exact congrArg (fun t : FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K) => t^[n] (x f)) hact
  rw [hpow]
  exact hcap f

end HarmonicArtin

end OAI
