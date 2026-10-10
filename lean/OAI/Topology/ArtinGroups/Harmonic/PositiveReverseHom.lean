import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ExtArrow
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefixMulLeft

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
include z hz

lemma reverse_wordPositive_braid (s t:S) :
    wordPositive M (altList s t (M s t)).reverse=wordPositive M (altList t s (M s t)).reverse := by
  apply wordPositive_eq_of_reduced M
  · exact (alternating_isReduced_of_longest M z hz s t).reverse
  · have h:=alternating_isReduced_of_longest M z hz t s
    rw [M.symmetric t s] at h
    exact h.reverse
  · change M.toCoxeterSystem.wordProd (altList s t (M s t)).reverse=M.toCoxeterSystem.wordProd (altList t s (M s t)).reverse
    rw [M.toCoxeterSystem.wordProd_reverse,M.toCoxeterSystem.wordProd_reverse,altList_braid]

private lemma reverse_presented_relations : ∀u v:FreeMonoid S,positiveBraidRelations M u v →
    FreeMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) u=
      FreeMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) v := by
  rintro u v ⟨s,t,rfl,rfl⟩
  apply MulOpposite.unop_injective
  simp only [FreeMonoid.lift_ofList,MulOpposite.unop_list_prod,List.map_map]
  change (List.map (positiveGenerator M) (altList s t (M s t))).reverse.prod =
    (List.map (positiveGenerator M) (altList t s (M s t))).reverse.prod
  simpa only [wordPositive, List.map_reverse] using reverse_wordPositive_braid M z hz s t

noncomputable def positiveReverseHom : PositiveArtin M →* (PositiveArtin M)ᵐᵒᵖ :=
  PresentedMonoid.lift (fun s=>MulOpposite.op (positiveGenerator M s)) (reverse_presented_relations M z hz)

noncomputable def positiveReverse (a:PositiveArtin M) : PositiveArtin M := (positiveReverseHom M z hz a).unop

@[simp] lemma positiveReverse_generator (s:S) : positiveReverse M z hz (positiveGenerator M s)=positiveGenerator M s :=rfl
@[simp] lemma positiveReverse_one : positiveReverse M z hz 1=1 :=by unfold positiveReverse;rw [map_one];rfl
lemma positiveReverse_mul (a b:PositiveArtin M) : positiveReverse M z hz (a*b)=positiveReverse M z hz b*positiveReverse M z hz a :=by unfold positiveReverse;rw [map_mul];rfl

lemma positiveReverse_word (w:List S) : positiveReverse M z hz (wordPositive M w)=wordPositive M w.reverse := by
  induction w with
  | nil=>exact positiveReverse_one M z hz
  | cons s w ih=>
    change positiveReverse M z hz (positiveGenerator M s*wordPositive M w)=_
    rw [positiveReverse_mul,positiveReverse_generator,ih,List.reverse_cons,wordPositive_append]
    rfl

@[simp] lemma positiveReverse_involutive (a:PositiveArtin M) : positiveReverse M z hz (positiveReverse M z hz a)=a :=by
  obtain ⟨w,rfl⟩:=positive_word_surjective M a
  rw [positiveReverse_word,positiveReverse_word,List.reverse_reverse]

def PositiveSuffix (a b:PositiveArtin M) : Prop := ∃c:PositiveArtin M,b=c*a

lemma positiveReverse_prefix_iff (a b:PositiveArtin M) :
    PositivePrefix M (positiveReverse M z hz a) (positiveReverse M z hz b) ↔ PositiveSuffix M a b := by
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨positiveReverse M z hz c,?_⟩
    have h:=congrArg (positiveReverse M z hz) hc
    simpa only [positiveReverse_mul,positiveReverse_involutive] using h
  · rintro ⟨c,hc⟩
    exact ⟨positiveReverse M z hz c,by rw [hc,positiveReverse_mul]⟩

theorem positive_greatest_common_right_divisor
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (a b:PositiveArtin M) :
    ∃g:PositiveArtin M,PositiveSuffix M g a ∧ PositiveSuffix M g b ∧
      ∀e:PositiveArtin M,PositiveSuffix M e a→PositiveSuffix M e b→PositiveSuffix M e g := by
  obtain ⟨g,hga,hgb,hgreat⟩:=positive_greatest_common_left_divisor M cancel z hz
    (positiveReverse M z hz a) (positiveReverse M z hz b)
  refine ⟨positiveReverse M z hz g,?_,?_,?_⟩
  · apply (positiveReverse_prefix_iff M z hz _ _).mp
    simpa only [positiveReverse_involutive] using hga
  · apply (positiveReverse_prefix_iff M z hz _ _).mp
    simpa only [positiveReverse_involutive] using hgb
  · intro e hea heb
    apply (positiveReverse_prefix_iff M z hz _ _).mp
    rw [positiveReverse_involutive]
    exact hgreat _ ((positiveReverse_prefix_iff M z hz _ _).mpr hea)
      ((positiveReverse_prefix_iff M z hz _ _).mpr heb)

end HarmonicArtin

end OAI
