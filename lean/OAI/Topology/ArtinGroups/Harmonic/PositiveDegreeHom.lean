import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRelations

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma positive_word_surjective (a:PositiveArtin M) : ∃w:List S,wordPositive M w=a := by
  obtain ⟨w,rfl⟩:=PresentedMonoid.surjective_mk a
  exact ⟨FreeMonoid.toList w,by rw [wordPositive_mk,FreeMonoid.ofList_toList]⟩

lemma positiveDegree_relations : ∀a b:FreeMonoid S,positiveBraidRelations M a b →
    FreeMonoid.lift (fun _ : S=>Multiplicative.ofAdd (1:ℕ)) a=
      FreeMonoid.lift (fun _ : S=>Multiplicative.ofAdd (1:ℕ)) b := by
  rintro a b ⟨s,t,rfl,rfl⟩
  simp [FreeMonoid.lift_ofList,List.map_const',List.prod_replicate,length_altList]

def positiveDegreeHom : PositiveArtin M →* Multiplicative ℕ :=
  PresentedMonoid.lift (fun _=>Multiplicative.ofAdd 1) (positiveDegree_relations M)

def positiveDegree (a:PositiveArtin M) : ℕ := Multiplicative.toAdd (positiveDegreeHom M a)

@[simp] lemma positiveDegree_one : positiveDegree M 1=0 :=rfl
@[simp] lemma positiveDegree_generator (s:S) : positiveDegree M (positiveGenerator M s)=1 :=rfl
@[simp] lemma positiveDegree_mul (a b:PositiveArtin M) :
    positiveDegree M (a*b)=positiveDegree M a+positiveDegree M b := by
  unfold positiveDegree
  rw [map_mul]
  rfl
@[simp] lemma positiveDegree_word (w:List S) : positiveDegree M (wordPositive M w)=w.length := by
  induction w with
  | nil=>rfl
  | cons s w ih=>
    change positiveDegree M (positiveGenerator M s*wordPositive M w)=w.length+1
    rw [positiveDegree_mul,positiveDegree_generator,ih,Nat.add_comm]

lemma positiveDegree_zero_iff (a:PositiveArtin M) : positiveDegree M a=0 ↔ a=1 := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveDegree_word]
  constructor
  · intro h;rw [List.eq_nil_of_length_eq_zero h];rfl
  · intro h;simpa only [positiveDegree_word,positiveDegree_one] using congrArg (positiveDegree M) h

lemma positiveToCoxeter_relations : ∀a b:FreeMonoid S,positiveBraidRelations M a b →
    FreeMonoid.lift M.toCoxeterSystem.simple a=FreeMonoid.lift M.toCoxeterSystem.simple b := by
  rintro a b ⟨s,t,rfl,rfl⟩
  simpa only [FreeMonoid.lift_ofList,CoxeterSystem.wordProd] using altList_braid M.toCoxeterSystem s t

def positiveToCoxeter : PositiveArtin M →* M.Group :=
  PresentedMonoid.lift M.toCoxeterSystem.simple (positiveToCoxeter_relations M)

@[simp] lemma positiveToCoxeter_generator (s:S) :
    positiveToCoxeter M (positiveGenerator M s)=M.toCoxeterSystem.simple s :=rfl

@[simp] lemma positiveToCoxeter_word (w:List S) :
    positiveToCoxeter M (wordPositive M w)=wordCoxeter M w := by
  induction w with
  | nil=>exact map_one _
  | cons s w ih=>
    change positiveToCoxeter M (positiveGenerator M s*wordPositive M w)=M.toCoxeterSystem.simple s*wordCoxeter M w
    rw [map_mul,positiveToCoxeter_generator,ih]

lemma positiveToCoxeter_length_le (a:PositiveArtin M) :
    M.toCoxeterSystem.length (positiveToCoxeter M a)≤positiveDegree M a := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveToCoxeter_word,positiveDegree_word]
  exact M.toCoxeterSystem.length_wordProd_le w

noncomputable def positiveSimpleLift (w:M.Group) : PositiveArtin M :=
  wordPositive M (reducedExpression M w)

@[simp] lemma positiveDegree_simpleLift (w:M.Group) :
    positiveDegree M (positiveSimpleLift M w)=M.toCoxeterSystem.length w := by
  rw [positiveSimpleLift,positiveDegree_word,←(reducedExpression_reduced M w).eq]
  change M.toCoxeterSystem.length (wordCoxeter M (reducedExpression M w))=_
  rw [wordCoxeter_reducedExpression]

@[simp] lemma positiveToCoxeter_simpleLift (w:M.Group) :
    positiveToCoxeter M (positiveSimpleLift M w)=w := by
  rw [positiveSimpleLift,positiveToCoxeter_word,wordCoxeter_reducedExpression]

lemma positiveSimpleLift_word [Finite S] (w:List S) (h:M.toCoxeterSystem.IsReduced w) :
    positiveSimpleLift M (wordCoxeter M w)=wordPositive M w := by
  exact wordPositive_eq_of_reduced M _ w (reducedExpression_reduced M _) h (wordCoxeter_reducedExpression M _)

lemma positive_eq_simpleLift_of_degree [Finite S] (a:PositiveArtin M)
    (h:M.toCoxeterSystem.length (positiveToCoxeter M a)=positiveDegree M a) :
    a=positiveSimpleLift M (positiveToCoxeter M a) := by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveToCoxeter_word,positiveDegree_word] at h
  rw [positiveToCoxeter_word]
  exact (positiveSimpleLift_word M w h).symm

end HarmonicArtin

end OAI
