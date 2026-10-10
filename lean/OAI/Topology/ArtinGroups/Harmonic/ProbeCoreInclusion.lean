import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbePositiveWord

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "R" => probeQuiver Q
local notation "hnR" => probeQuiver_no_loops Q hn

abbrev probeCoreInclusion (J:Set S) (α:J × FusionLabel m) : ProbeVertex (FusionVertex (V:=S⊕Unit) m) :=
  Sum.inl (unfoldedInclusion M J α)

omit [Fintype S] in
lemma probeCoreInclusion_injective (J:Set S) : Function.Injective (probeCoreInclusion M J) :=
  fun _ _ he=>unfoldedInclusion_injective M J (Sum.inl.inj he)

lemma probeCore_matrix (J:Set S) (hJ:IsSpherical M J) (α β:J × FusionLabel m) :
    ordinaryCoxeterMatrix R (probeCoreInclusion M J α) (probeCoreInclusion M J β)=
      unfoldedMatrix M J α β := by
  rcases unfolded_full_simply_laced M J hJ (unfoldedInclusion M J α) ⟨α,rfl⟩
    (unfoldedInclusion M J β) ⟨β,rfl⟩ with he | hrest
  · have h:=unfoldedInclusion_injective M J he
    subst β
    simp
  · rcases hrest with ho | hedge
    · rw [← unfolded_ordinaryMatrix M J hJ,ordinaryCoxeterMatrix_orthogonal Q ho]
      exact ordinaryCoxeterMatrix_orthogonal R (probe_orthogonal Q ho)
    · obtain ⟨e⟩:=hedge
      rw [← unfolded_ordinaryMatrix M J hJ,ordinaryCoxeterMatrix_adjacent Q e]
      exact ordinaryCoxeterMatrix_adjacent R (probe_simpleEdge Q e)

lemma probeCore_simply_laced (J:Set S) (hJ:IsSpherical M J) :
    ∀ α∈Set.range (probeCoreInclusion M J),∀ β∈Set.range (probeCoreInclusion M J),
      α=β ∨ OrthogonalVertices R α β ∨ Nonempty (SimpleEdge R α β) := by
  rintro _ ⟨α,rfl⟩ _ ⟨β,rfl⟩
  rcases unfolded_full_simply_laced M J hJ _ ⟨α,rfl⟩ _ ⟨β,rfl⟩ with he | hrest
  · exact Or.inl (congrArg Sum.inl he)
  · rcases hrest with ho | hedge
    · exact Or.inr (Or.inl (probe_orthogonal Q ho))
    · obtain ⟨e⟩:=hedge
      exact Or.inr (Or.inr ⟨probe_simpleEdge Q e⟩)

lemma probePositiveWord_core_expanded (J:Set S) (w:List J) (x:FiniteHomotopyClass R (K:=K)) :
    probePositiveWord M J w x=positiveWordAction R
      ((fusionExpandedWord m w).map (probeCoreInclusion M J)) x := by
  simpa only [fusionExpandedWord_map,List.map_map,Function.comp_def,
    probeCoreInclusion,unfoldedInclusion] using probePositiveWord_expanded M J w x

lemma probeCore_word_support (J:Set S) (w:List J) :
    ∀ α∈(fusionExpandedWord m w).map (probeCoreInclusion M J),
      α∈Set.range (probeCoreInclusion M J) := by
  intro α hα
  obtain ⟨β,_,rfl⟩:=List.mem_map.mp hα
  exact ⟨β,rfl⟩

lemma probePositiveWord_testUpper_reflect (J:Set S) (w:List J)
    (x:FiniteHomotopyClass R (K:=K)) {t:ℤ}
    (h:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) t) :
    ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t := by
  rw [probePositiveWord_core_expanded] at h
  exact positiveWordAction_testUpper_reflect R hnR _ x _ (probeCore_word_support M J w) h

lemma probeCore_cons_reduced (J:Set S) (hJ:IsSpherical M J) (w:List J) (j:J)
    (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w)
    (hj:(restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w)) (L:FusionLabel m) :
    (ordinaryCoxeterMatrix R).toCoxeterSystem.IsReduced
      (probeCoreInclusion M J (j,L)::(fusionExpandedWord m w).map (probeCoreInclusion M J)) := by
  apply embedding_reduced (probeCoreInclusion M J) (probeCoreInclusion_injective M J)
    (probeCore_matrix M J hJ) ((j,L)::fusionExpandedWord m w)
  have hr:=unfolded_reducedWord M J hJ w hw
  change (unfoldedMatrix M J).toCoxeterSystem.length
    ((unfoldedMatrix M J).toCoxeterSystem.simple (j,L)*
      (unfoldedMatrix M J).toCoxeterSystem.wordProd (fusionExpandedWord m w))=
    (fusionExpandedWord m w).length+1
  rw [← unfoldedHom_wordProd M J hJ]
  have ha: (restrictedMatrix M J).toCoxeterSystem.length
      ((restrictedMatrix M J).toCoxeterSystem.simple j*
        (restrictedMatrix M J).toCoxeterSystem.wordProd w)=
      (restrictedMatrix M J).toCoxeterSystem.length
        ((restrictedMatrix M J).toCoxeterSystem.wordProd w)+1 := by
    rw [hw.eq]
    exact hj.eq
  rw [(unfoldedHom_left_ascent M J hJ _ (j,L)).mpr ha,unfoldedHom_wordProd,hr.eq]

theorem probe_reduced_ascent_top_exact (J:Set S) (hJ:IsSpherical M J)
    (w:List J) (j:J) (hw:(restrictedMatrix M J).toCoxeterSystem.IsReduced w)
    (hj:(restrictedMatrix M J).toCoxeterSystem.IsReduced (j::w))
    (x:FiniteHomotopyClass R (K:=K)) (t ℓ:ℤ) (hlt:t<ℓ)
    (hx:ClassTestUpper R x (Set.range (probeCoreInclusion M J)) t)
    (hy:ClassTestUpper R (probePositiveWord M J w x) (Set.range (probeCoreInclusion M J)) ℓ)
    (L:FusionLabel m) (c:ℤ) :
    ClassTestExact R (probeCoreInclusion M J (j,L)) ℓ c (probePositiveWord M J w x) := by
  rw [probePositiveWord_core_expanded] at hy ⊢
  by_contra hc
  obtain ⟨v,hv⟩:=positive_top_divisor R hnR _ (probeCore_simply_laced M J hJ)
    x t hx _ (probeCore_word_support M J w) _ ⟨(j,L),rfl⟩ ℓ hlt hy c hc
  exact reduced_no_top_divisor R (probeCore_cons_reduced M J hJ w j hw hj L) hv

end HarmonicArtin

end OAI
