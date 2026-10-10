import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ReducedExpression

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

def positiveBraidRelations (u v:FreeMonoid S) : Prop :=
  ∃s t:S,u=FreeMonoid.ofList (altList s t (M s t)) ∧ v=FreeMonoid.ofList (altList t s (M s t))

abbrev PositiveArtin := PresentedMonoid (positiveBraidRelations M)

def positiveGenerator (s:S) : PositiveArtin M := PresentedMonoid.of (positiveBraidRelations M) s

def wordPositive (w:List S) : PositiveArtin M := (w.map (positiveGenerator M)).prod

lemma wordPositive_mk (w:List S) : wordPositive M w=PresentedMonoid.mk (positiveBraidRelations M) (FreeMonoid.ofList w) := by
  induction w with
  | nil=>rfl
  | cons s w ih=>
    change positiveGenerator M s*wordPositive M w=PresentedMonoid.mk (positiveBraidRelations M) (FreeMonoid.of s*FreeMonoid.ofList w)
    rw [map_mul,←ih];rfl

lemma wordPositive_braid (s t:S) : wordPositive M (altList s t (M s t))=wordPositive M (altList t s (M s t)) := by
  rw [wordPositive_mk,wordPositive_mk]
  exact PresentedMonoid.mk_eq_mk_of_rel ⟨s,t,rfl,rfl⟩

lemma wordPositive_append (u v:List S) : wordPositive M (u++v)=wordPositive M u*wordPositive M v := by
  simp only [wordPositive,List.map_append,List.prod_append]

lemma wordPositive_eq_of_reduced [Finite S] (u v:List S)
    (hu:M.toCoxeterSystem.IsReduced u) (hv:M.toCoxeterSystem.IsReduced v)
    (he:wordCoxeter M u=wordCoxeter M v) : wordPositive M u=wordPositive M v := by
  classical
  let := Fintype.ofFinite S
  exact reduced_word_property M.toCoxeterSystem (positiveGenerator M) (wordPositive_braid M) u v hu hv he

lemma positiveToArtin_relations : ∀u v:FreeMonoid S,positiveBraidRelations M u v →
    FreeMonoid.lift (generator M) u=FreeMonoid.lift (generator M) v := by
  rintro u v ⟨s,t,rfl,rfl⟩
  simpa only [FreeMonoid.lift_ofList,wordArtin] using wordArtin_braid M s t

def positiveToArtin : PositiveArtin M →* Artin M :=
  PresentedMonoid.lift (generator M) (positiveToArtin_relations M)

@[simp] lemma positiveToArtin_generator (s:S) : positiveToArtin M (positiveGenerator M s)=generator M s :=rfl

@[simp] lemma positiveToArtin_word (w:List S) : positiveToArtin M (wordPositive M w)=wordArtin M w := by
  induction w with
  | nil=>exact map_one _
  | cons s w ih=>
    change positiveToArtin M (positiveGenerator M s*wordPositive M w)=generator M s*wordArtin M w
    rw [map_mul,positiveToArtin_generator,ih]

end HarmonicArtin

end OAI
