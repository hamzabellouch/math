import OAI.Topology.ArtinGroups.ParabolicIntersections.ReducedPositiveExtension
import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingGcdInput
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedFamily
import OAI.Topology.ArtinGroups.Harmonic.ArtinActionWordArtin

namespace OAI

/-! Common positive extensions with the actual total test-height bound. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "hn" => fusionQuiver_no_loops m (coxeterFusionEdge M)
  (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)

noncomputable def restrictedPointedFamily (Y : Set S) (x : Artin M)
    (a : Artin (restrictedMatrix M Y)) : PointedFamilySpace M :=
  pointedFamily M f (restrictedArtinHom M Y a*x)

lemma restrictedPointedFamily_word (Y : Set S) (x : Artin M)
    (u : List Y) (a : Artin (restrictedMatrix M Y)) (L : PointedLabel M) :
    restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L =
      positiveWordAction Q
        (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
        (restrictedPointedFamily M f Y x a L) := by
  unfold restrictedPointedFamily pointedFamily
  rw [positiveToArtin_word, map_mul (restrictedArtinHom M Y),
    restrictedArtinHom_word, _root_.mul_assoc]
  rw [map_mul, Equiv.Perm.mul_apply]
  simpa only [pointedAction, List.map_map, Function.comp_def] using
    sourceArtinAction_positiveWord M (u.map Subtype.val)
      (pointedAction M (restrictedArtinHom M Y a*x) (pointedInitial M f L))

private lemma testUpper_eventually (x : FiniteHomotopyClass Q (K := ℂ))
    (U : Set (FusionVertex (V := S⊕Unit) m)) (t : ℤ) :
    ∃ n : ℕ, ClassTestUpper Q x U (t+n) := by
  obtain ⟨b,hb⟩ := Finite.bddAbove_range (fun i : (minimalClassModel Q x).Index =>
    ((minimalClassModel Q x).complex.placement i).level)
  have h := classTestUpper_of_generator_cap Q x b (fun i => hb (Set.mem_range_self i)) U
  refine ⟨(b+2-t).toNat, ?_⟩
  intro α hα l hl c
  apply h α hα l _ c
  have : b+2-t ≤ ((b+2-t).toNat : ℤ) := by omega
  omega

/-- Lemma 7.5: a common positive left extension preserves a common bound
on the total test heights. Only published admissible-folding gcd
preservation is assumed; the top-test argument is proved here. -/
theorem spherical_common_extension (Y : Set S) (hY : IsSpherical M Y)
    (hGcd : PublishedFoldingGcd M Y hY) (x : Artin M)
    (a b : Artin (restrictedMatrix M Y)) (t : ℤ)
    (ha : ∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x a L)
      (Set.range (unfoldedInclusion M Y)) t)
    (hb : ∀ L, ClassTestUpper Q (restrictedPointedFamily M f Y x b L)
      (Set.range (unfoldedInclusion M Y)) t) :
    ∃ p q : PositiveArtin (restrictedMatrix M Y),
      positiveToArtin _ p*a=positiveToArtin _ q*b ∧
      ∀ L, ClassTestUpper Q
        (restrictedPointedFamily M f Y x (positiveToArtin _ p*a) L)
        (Set.range (unfoldedInclusion M Y)) t := by
  obtain ⟨p,q,he,hdisjoint⟩ := spherical_reduced_positive_extension M Y hY a b
  refine ⟨p,q,he,?_⟩
  intro L
  by_contra hbad
  obtain ⟨u,rfl⟩ := positive_word_surjective _ p
  obtain ⟨v,rfl⟩ := positive_word_surjective _ q
  let z := restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L
  let U := Set.range (unfoldedInclusion M Y)
  obtain ⟨l,hl,hcap,α,hα,c,hnot⟩ := exists_top_test Q z U t
    (testUpper_eventually M z U t) hbad
  have hletters (w : List Y) : ∀ β ∈ fusionExpandedWord m
      (w.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)), β ∈ U := by
    intro β hβ
    have h : β.1 ∈ w.map (fun j : Y => (Sum.inl (j:S) : S⊕Unit)) :=
      fusionExpandedWord_mem m _ β hβ
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    exact ⟨(i,β.2), Prod.ext hi rfl⟩
  have hzU : z=positiveWordAction Q
      (fusionExpandedWord m (u.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
      (restrictedPointedFamily M f Y x a L) := restrictedPointedFamily_word M f Y x u a L
  have hzV : z=positiveWordAction Q
      (fusionExpandedWord m (v.map fun j : Y => (Sum.inl (j:S) : S⊕Unit)))
      (restrictedPointedFamily M f Y x b L) := by
    change restrictedPointedFamily M f Y x (positiveToArtin _ (wordPositive _ u)*a) L = _
    rw [he]
    exact restrictedPointedFamily_word M f Y x v b L
  obtain ⟨r,hr⟩ := positive_top_divisor Q hn U (unfolded_full_simply_laced M Y hY)
    (restrictedPointedFamily M f Y x a L) t (ha L) _ (hletters u) α hα l hl
    (hzU ▸ hcap) c (hzU ▸ hnot)
  obtain ⟨s,hs⟩ := positive_top_divisor Q hn U (unfolded_full_simply_laced M Y hY)
    (restrictedPointedFamily M f Y x b L) t (hb L) _ (hletters v) α hα l hl
    (hzV ▸ hcap) c (hzV ▸ hnot)
  obtain ⟨i,hi⟩ := hGcd.common_atom u v α r s hr hs
  exact hdisjoint i hi

end HarmonicArtin.ParabolicIntersections

end OAI
