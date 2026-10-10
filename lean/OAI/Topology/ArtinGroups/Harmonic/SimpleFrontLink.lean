import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def SimpleFrontLink (a:PositiveArtin M) (s t:S) : Prop :=
  ∃w:M.Group,PositivePrefix M (positiveSimpleLift M w) a ∧
    PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M w) ∧
    PositivePrefix M (positiveGenerator M t) (positiveSimpleLift M w)

def FrontLinked (a:PositiveArtin M) : S→S→Prop := Relation.ReflTransGen (SimpleFrontLink M a)

omit [Fintype S] in
lemma simpleFrontLink_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:SimpleFrontLink M a s t) : SimpleFrontLink M b s t := by
  obtain ⟨w,hwa,hs,ht⟩:=h
  exact ⟨w,positivePrefix_trans M hwa hab,hs,ht⟩

omit [Fintype S] in
lemma frontLinked_mono {a b:PositiveArtin M} (hab:PositivePrefix M a b) {s t:S}
    (h:FrontLinked M a s t) : FrontLinked M b s t := by
  induction h with
  | refl=>exact .refl
  | tail h hst ih=>exact ih.tail (simpleFrontLink_mono M hab hst)

omit [Fintype S] in
lemma frontLinked_symm {a:PositiveArtin M} {s t:S} (h:FrontLinked M a s t) : FrontLinked M a t s := by
  induction h with
  | refl=>exact .refl
  | @tail u v h huv ih=>
    obtain ⟨w,hwa,hu,hv⟩:=huv
    exact (Relation.ReflTransGen.single ⟨w,hwa,hv,hu⟩).trans ih

lemma alternating_isReduced_of_longest (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s t:S) :
    M.toCoxeterSystem.IsReduced (altList s t (M s t)) := by
  by_cases he:s=t
  · subst t
    simpa only [M.diagonal s,altList_succ,altList_zero] using
      (show M.toCoxeterSystem.IsReduced [s] from by
        change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
        exact M.toCoxeterSystem.length_simple s)
  · have hs:WeakPrefix M.toCoxeterSystem (M.toCoxeterSystem.simple s) z:=
      (positivePrefix_simple_iff M _ _).mp (by
        exact ⟨positiveSimpleLift M ((M.toCoxeterSystem.simple s)⁻¹*z),
          (positiveSimpleLift_left_complement M z hz _).symm⟩)
    have ht:WeakPrefix M.toCoxeterSystem (M.toCoxeterSystem.simple t) z:=
      (positivePrefix_simple_iff M _ _).mp (by
        exact ⟨positiveSimpleLift M ((M.toCoxeterSystem.simple t)⁻¹*z),
          (positiveSimpleLift_left_complement M z hz _).symm⟩)
    obtain ⟨v,hm,hl,hv,hv'⟩:=double_descent_prefix M.toCoxeterSystem s t he z
      (by have h:=(weakPrefix_simple_iff M.toCoxeterSystem s z).mp hs;omega)
      (by have h:=(weakPrefix_simple_iff M.toCoxeterSystem t z).mp ht;omega)
    have h₁:=M.toCoxeterSystem.length_wordProd_le (altList s t (M s t))
    have h₂:=M.toCoxeterSystem.length_mul_le (M.toCoxeterSystem.wordProd (altList s t (M s t))) v
    rw [←hv] at h₂
    change M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd (altList s t (M s t)))=(altList s t (M s t)).length
    rw [length_altList] at h₁ ⊢
    omega

lemma wordPositive_simple_of_reduced (w:List S) (hw:M.toCoxeterSystem.IsReduced w) :
    wordPositive M w=positiveSimpleLift M (wordCoxeter M w) :=
  (positiveSimpleLift_word M w hw).symm

omit [Fintype S] in
lemma positivePrefix_first (s:S) (w:List S) : PositivePrefix M (positiveGenerator M s) (wordPositive M (s::w)) :=⟨wordPositive M w,rfl⟩

end HarmonicArtin

end OAI
