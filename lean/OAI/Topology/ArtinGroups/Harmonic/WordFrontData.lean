import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.SimpleFrontLink

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

private def WordFrontData (u v:List S) : Prop :=
  wordPositive M u=wordPositive M v ∧ u.length=v.length ∧
    ∀s us t vs,u=s::us→v=t::vs→FrontLinked M (wordPositive M u) s t

omit [Fintype S] in
private lemma wordFront_refl (u:List S) : WordFrontData M u u := by
  refine ⟨rfl,rfl,?_⟩
  intro s us t vs hu hv
  have h:s=t:=by simpa only [hu,List.cons.injEq] using (List.cons.inj (hu.symm.trans hv)).1
  subst t
  exact .refl

omit [Fintype S] in
private lemma wordFront_symm {u v:List S} (h:WordFrontData M u v) : WordFrontData M v u := by
  refine ⟨h.1.symm,h.2.1.symm,?_⟩
  intro s us t vs hu hv
  rw [←h.1]
  exact frontLinked_symm M (h.2.2 t vs s us hv hu)

omit [Fintype S] in
private lemma wordFront_trans {u v w:List S} (h:WordFrontData M u v) (k:WordFrontData M v w) : WordFrontData M u w := by
  refine ⟨h.1.trans k.1,h.2.1.trans k.2.1,?_⟩
  intro s us t ts hu hw
  cases v with
  | nil=>have hh:=h.2.1;rw [hu] at hh;simp at hh
  | cons r rs=>
    have hl:=h.2.2 s us r rs hu rfl
    have hr:=k.2.2 r rs t ts rfl hw
    rw [←h.1] at hr
    exact hl.trans hr

omit [Fintype S] in
private lemma wordFront_mul {u v w x:List S} (h:WordFrontData M u v) (k:WordFrontData M w x) : WordFrontData M (u++w) (v++x) := by
  refine ⟨by rw [wordPositive_append,wordPositive_append,h.1,k.1],by simp only [List.length_append,h.2.1,k.2.1],?_⟩
  intro s us t ts hu hv
  cases u with
  | nil=>
    have he:v=[]:=List.length_eq_zero_iff.mp h.2.1.symm
    subst v
    exact k.2.2 s us t ts hu hv
  | cons r rs=>
    cases v with
    | nil=>have hh:=h.2.1;simp at hh
    | cons q qs=>
      have hs:r=s:=(List.cons.inj hu).1
      have ht:q=t:=(List.cons.inj hv).1
      subst s;subst t
      exact frontLinked_mono M ⟨wordPositive M w,wordPositive_append M _ _⟩
        (h.2.2 r rs q qs rfl rfl)

private lemma wordFront_relation (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s t:S) :
    WordFrontData M (altList s t (M s t)) (altList t s (M s t)) := by
  refine ⟨wordPositive_braid M s t,by simp only [length_altList],?_⟩
  intro r rs q qs hr hq
  by_cases hm:M s t=0
  · rw [hm,altList_zero] at hr
    contradiction
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hm
  have hs:s=r:=by rw [hn,altList_succ] at hr;exact (List.cons.inj hr).1
  have ht:t=q:=by rw [hn,altList_succ] at hq;exact (List.cons.inj hq).1
  subst r;subst q
  have hred:=alternating_isReduced_of_longest M z hz s t
  have he:=wordPositive_simple_of_reduced M _ hred
  apply Relation.ReflTransGen.single
  refine ⟨wordCoxeter M (altList s t (M s t)),he ▸ positivePrefix_refl M _,?_,?_⟩
  · rw [←he,hr]
    exact positivePrefix_first M s rs
  · rw [←he,wordPositive_braid,hq]
    exact positivePrefix_first M t qs

private lemma wordFront_conGen (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    {u v:FreeMonoid S} (h:ConGen.Rel (positiveBraidRelations M) u v) :
    WordFrontData M u.toList v.toList := by
  induction h with
  | of a b h=>
    obtain ⟨s,t,rfl,rfl⟩:=h
    exact wordFront_relation M z hz s t
  | refl a=>exact wordFront_refl M a.toList
  | symm h ih=>exact wordFront_symm M ih
  | trans h k ih ik=>exact wordFront_trans M ih ik
  | mul h k ih ik=>exact wordFront_mul M ih ik

theorem positive_first_letters_connected (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) (s t:S)
    (hs:PositivePrefix M (positiveGenerator M s) a)
    (ht:PositivePrefix M (positiveGenerator M t) a) : FrontLinked M a s t := by
  obtain ⟨b,hb⟩:=hs
  obtain ⟨c,hc⟩:=ht
  obtain ⟨u,hu⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) b
  obtain ⟨v,hv⟩:=PresentedMonoid.surjective_mk (rels:=positiveBraidRelations M) c
  have hu':wordPositive M u.toList=b:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hu]
  have hv':wordPositive M v.toList=c:=by rw [wordPositive_mk,FreeMonoid.ofList_toList,hv]
  have he₁:wordPositive M (s::u.toList)=a:=by change positiveGenerator M s*wordPositive M u.toList=a;rw [hu',←hb]
  have he₂:wordPositive M (t::v.toList)=a:=by change positiveGenerator M t*wordPositive M v.toList=a;rw [hv',←hc]
  have he:=he₁.trans he₂.symm
  rw [wordPositive_mk,wordPositive_mk] at he
  have h:ConGen.Rel (positiveBraidRelations M) (FreeMonoid.ofList (s::u.toList)) (FreeMonoid.ofList (t::v.toList)):=PresentedMonoid.mk_eq_mk_iff.mp he
  have hf:=(wordFront_conGen M z hz h).2.2 s u.toList t v.toList rfl rfl
  rw [FreeMonoid.toList_ofList,he₁] at hf
  exact hf

end HarmonicArtin

end OAI
