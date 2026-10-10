import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.CanonicalReducedWordLow
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedInclusion
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLowExpansion

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] {K : Type*} [Field K]
  (M : CoxeterMatrix S)
local notation "Q" => fusionQuiver (fusionLabelSize M) (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
local notation "C" => canonicalFusionLow (fusionLabelSize M) (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M) (K:=K)

lemma unfolded_full_word_mem (J : Set S) (u : List J) :
    ∀ α∈fusionExpandedWord (fusionLabelSize M) (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)),
      α∈Set.range (unfoldedInclusion M J) := by
  intro α hα
  have hh:=fusionExpandedWord_mem (fusionLabelSize M) _ α hα
  obtain ⟨j,_,hj⟩:=List.mem_map.mp hh
  exact ⟨(j,α.2),Prod.ext hj rfl⟩

lemma sourceCanonicalLow_eq (J : Set S) (u : List J) (q : ℤ)
    (x : FiniteHomotopyClass Q (K:=K)) :
    C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x =
      canonicalWordLow Q (fusionExpandedWord (fusionLabelSize M)
        (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) q x := by
  convert canonicalFusionLow_eq_expansion (fusionLabelSize M) (coxeterFusionEdge M)
    (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
    (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x using 1
  exact congrArg (fun decEq : DecidableEq (FusionQuiverArrow (fusionLabelSize M) (coxeterFusionEdge M)) =>
    @canonicalWordLow _ _ K Q _ _ _ _ decEq (fusionExpandedWord (fusionLabelSize M)
      (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit))) q x) (Subsingleton.elim _ _)

theorem sourceCanonicalLow_termwiseSplit (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    Nonempty (TermwiseSplitInjection Q
      (minimalClassModel Q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x)).complex
      (minimalClassModel Q x).complex) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalReducedWordLow_termwiseSplit Q hn (Set.range (unfoldedInclusion M J))
    (unfolded_full_simply_laced M J hJ) x q hlo hhi _ (unfolded_full_word_mem M J u)
    (unfolded_full_reduced M J hJ u hu)

theorem sourceCanonicalLow_pure (J : Set S) (hJ : IsSpherical M J)
    (u : List J) (hu : (restrictedMatrix M J).toCoxeterSystem.IsReduced u)
    (q : ℤ) (x : FiniteHomotopyClass Q (K:=K))
    (hlo : ClassLowerBound Q q x) (hhi : ClassUpperBound Q q x) :
    ClassLowerBound Q q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x) ∧
      ClassUpperBound Q q (C (u.map fun j : J => (Sum.inl (j:S) : S⊕Unit)) q x) := by
  rw [sourceCanonicalLow_eq]
  exact canonicalReducedWordLow_pure Q hn (Set.range (unfoldedInclusion M J))
    (unfolded_full_simply_laced M J hJ) x q hlo hhi _ (unfolded_full_word_mem M J u)
    (unfolded_full_reduced M J hJ u hu)

end HarmonicArtin

end OAI
