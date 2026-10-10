import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverSimpleEdge
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedColorOrthogonal
import OAI.Topology.ArtinGroups.Coxeter.WordProdEquiv

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S]

abbrev unfoldedInclusion (M : CoxeterMatrix S) (J : Set S)
    (α : J × FusionLabel (fusionLabelSize M)) : FusionVertex (V:=S⊕Unit) (fusionLabelSize M) :=
  (Sum.inl α.1.val,α.2)

omit [Fintype S] in
lemma unfoldedInclusion_injective (M : CoxeterMatrix S) (J : Set S) :
    Function.Injective (unfoldedInclusion M J) := by
  intro α β h
  exact Prod.ext (Subtype.ext (Sum.inl.inj (Prod.mk.inj h).1)) (Prod.mk.inj h).2

variable (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

lemma unfolded_ordinaryMatrix (J : Set S) (hJ : IsSpherical M J)
    (α β : J × FusionLabel (fusionLabelSize M)) :
    ordinaryCoxeterMatrix Q (unfoldedInclusion M J α) (unfoldedInclusion M J β)=
      unfoldedMatrix M J α β := by
  by_cases he : α=β
  · subst β
    simp
  · have hi := fun hh => he (unfoldedInclusion_injective M J hh)
    have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
    have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=0 ∨
      (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
        (fusionLabelSize M) α.2 β.2=1 := by omega
    rcases hp with hz|ho
    · have horth := fusionQuiver_orthogonal (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi hz
      rw [ordinaryCoxeterMatrix_orthogonal Q horth,unfoldedMatrix_apply,ite_eq_right he,ite_eq_left hz]
    · let edge := fusionQuiver_simpleEdge (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (unfoldedInclusion M J α) (unfoldedInclusion M J β) hi ho
      rw [ordinaryCoxeterMatrix_adjacent Q edge,unfoldedMatrix_apply,ite_eq_right he,ho]
      norm_num

lemma unfolded_full_simply_laced (J : Set S) (hJ : IsSpherical M J) :
    ∀ α∈Set.range (unfoldedInclusion M J),∀ β∈Set.range (unfoldedInclusion M J),
      α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β) := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  by_cases he : α=β
  · exact Or.inl (congrArg _ he)
  have hi := fun hh => he (unfoldedInclusion_injective M J hh)
  have hn := spherical_fusion_multiplicity_le_one M J hJ α.1 β.1 α.2 β.2
  have hp : (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=0 ∨
    (coxeterFusionEdge M (.inl α.1) (.inl β.1)).multiplicity
      (fusionLabelSize M) α.2 β.2=1 := by omega
  rcases hp with hz|ho
  · exact Or.inr (Or.inl (fusionQuiver_orthogonal _ _ _ _ _ hi hz))
  · exact Or.inr (Or.inr ⟨fusionQuiver_simpleEdge _ _ _ _ _ hi ho⟩)

lemma fusionExpandedWord_map {E V T : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (f : V → T) (u : List V) :
    fusionExpandedWord m (u.map f)=(fusionExpandedWord m u).map (fun α => (f α.1,α.2)) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simp only [List.map_cons,fusionExpandedWord,List.flatMap_cons,List.map_append,List.map_map]
    congr 1

theorem unfolded_full_reduced (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u) :
    (ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced
      (fusionExpandedWord (fusionLabelSize M) (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) := by
  rw [fusionExpandedWord_map]
  exact embedding_reduced (unfoldedInclusion M J) (unfoldedInclusion_injective M J)
    (unfolded_ordinaryMatrix M J hJ) _ (unfolded_reducedWord M J hJ u hu)

lemma fusionExpandedWord_mem {E V : Type*} [Fintype E] [DecidableEq E]
    (m : E → ℕ) (u : List V) (α : V × FusionLabel m)
    (hα : α∈fusionExpandedWord m u) : α.1∈u := by
  obtain ⟨i,hi,hα⟩ := List.mem_flatMap.mp hα
  obtain ⟨L,_,rfl⟩ := List.mem_map.mp hα
  exact hi

end HarmonicArtin

end OAI
