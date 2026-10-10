import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingGcdInput
import OAI.Topology.ArtinGroups.Harmonic.UnfoldedColorOrthogonal
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelLeft

namespace OAI

/-! Positive-monoid folding and its action on simple elements. These are
proved from the Coxeter word theorem and the established folding geometry. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "m" => fusionLabelSize M

private lemma folded_word_product (w : List Y) :
    (w.map (fun i => wordPositive N (fusionExpandedWord m [i]))).prod =
      wordPositive N (fusionExpandedWord m w) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.map_cons,List.prod_cons,ih]
    simpa only [fusionExpandedWord, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      (wordPositive_append N (fusionExpandedWord m [i]) (fusionExpandedWord m w)).symm

include hY in
private lemma folded_positive_relations :
    ∀ a b : FreeMonoid Y, positiveBraidRelations R a b →
      FreeMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i])) a =
      FreeMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i])) b := by
  rintro a b ⟨i,j,rfl,rfl⟩
  simp only [FreeMonoid.lift_ofList,folded_word_product]
  let : Finite (R).Group := restricted_finite M Y hY
  obtain ⟨z,hz⟩ := exists_longest (R).toCoxeterSystem
  apply wordPositive_eq_of_reduced N
  · exact unfolded_reducedWord M Y hY _ (alternating_isReduced_of_longest R z hz i j)
  · rw [(R).symmetric i j]
    exact unfolded_reducedWord M Y hY _ (alternating_isReduced_of_longest R z hz j i)
  · exact unfolded_word_eq M Y hY _ _ (altList_braid (R).toCoxeterSystem i j)

noncomputable def foldedPositiveHom : PositiveArtin R →* PositiveArtin N :=
  PresentedMonoid.lift (fun i => wordPositive N (fusionExpandedWord m [i]))
    (folded_positive_relations M Y hY)

@[simp] lemma foldedPositiveHom_generator (i : Y) :
    foldedPositiveHom M Y hY (positiveGenerator R i)=
      wordPositive N (fusionExpandedWord m [i]) := rfl

lemma foldedPositiveHom_word (w : List Y) :
    foldedPositiveHom M Y hY (wordPositive R w)=wordPositive N (fusionExpandedWord m w) := by
  unfold wordPositive
  rw [map_list_prod]
  simp only [List.map_map,Function.comp_def,foldedPositiveHom_generator]
  exact folded_word_product M Y w

lemma foldedPositiveHom_simpleLift (w : (R).Group) :
    foldedPositiveHom M Y hY (positiveSimpleLift R w)=
      positiveSimpleLift N (unfoldedHom M Y hY w) := by
  change foldedPositiveHom M Y hY (wordPositive R (reducedExpression R w))=_
  rw [foldedPositiveHom_word]
  have hu := unfolded_reducedWord M Y hY _ (reducedExpression_reduced R w)
  have hw : (N).toCoxeterSystem.wordProd (fusionExpandedWord m (reducedExpression R w)) =
      unfoldedHom M Y hY w := by
    rw [← unfoldedHom_wordProd]
    exact congrArg (unfoldedHom M Y hY) (wordCoxeter_reducedExpression R w)
  rw [←hw]
  exact (positiveSimpleLift_word N _ hu).symm

/-- A left atom divides the folded simple element precisely when its
original color divides the original simple element. -/
theorem folded_simple_atom_iff (w : (R).Group) (α : Y × FusionLabel m) :
    PositivePrefix N (positiveGenerator N α)
      (foldedPositiveHom M Y hY (positiveSimpleLift R w)) ↔
    PositivePrefix R (positiveGenerator R α.1) (positiveSimpleLift R w) := by
  rw [foldedPositiveHom_simpleLift,←positiveSimpleLift_simple N α,
    ←positiveSimpleLift_simple R α.1,positivePrefix_simple_iff,positivePrefix_simple_iff,
    weakPrefix_simple_iff,weakPrefix_simple_iff]
  have h := unfoldedHom_left_ascent M Y hY w α
  have hn := (N).toCoxeterSystem.length_simple_mul (unfoldedHom M Y hY w) α
  have hr := (R).toCoxeterSystem.length_simple_mul w α.1
  dsimp only at h
  omega

end HarmonicArtin.ParabolicIntersections

end OAI
