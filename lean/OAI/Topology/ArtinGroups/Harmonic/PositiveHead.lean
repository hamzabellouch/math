import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.WordFrontData

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def HasPositiveHead (a:PositiveArtin M) : Prop :=
  ∃h:M.Group,PositivePrefix M (positiveSimpleLift M h) a ∧
    ∀w:M.Group,PositivePrefix M (positiveSimpleLift M w) a→
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h)

private def IsFrontHead (a:PositiveArtin M) (s:S) (h:M.Group) : Prop :=
  PositivePrefix M (positiveSimpleLift M h) a ∧
    PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M h) ∧
    ∀w:M.Group,PositivePrefix M (positiveSimpleLift M w) a→
      PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M w)→
      PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M h)

private lemma exists_front_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M)
    (ih:∀b:PositiveArtin M,positiveDegree M b<positiveDegree M a→HasPositiveHead M b)
    (s:S) (hs:PositivePrefix M (positiveGenerator M s) a) :
    ∃h:M.Group,IsFrontHead M a s h := by
  obtain ⟨b,hb⟩:=hs
  have hdeg:positiveDegree M b<positiveDegree M a:=by rw [hb,positiveDegree_mul,positiveDegree_generator];omega
  obtain ⟨g,hgb,hgreat⟩:=ih b hdeg
  let c: M.Group:=(M.toCoxeterSystem.simple s)⁻¹*z
  have hsc:positiveGenerator M s*positiveSimpleLift M c=positiveSimpleLift M z:=by
    simpa only [positiveSimpleLift_simple] using positiveSimpleLift_left_complement M z hz (M.toCoxeterSystem.simple s)
  obtain ⟨k,hkg,hkc,hmeet⟩:=exists_greatest_common_simplePrefix M g c
  let x:PositiveArtin M:=positiveGenerator M s*positiveSimpleLift M k
  have hxb:PositivePrefix M x a:=by
    obtain ⟨r,hr⟩:=positivePrefix_trans M hkg hgb
    refine ⟨r,?_⟩
    rw [hb,hr,mul_assoc]
  have hxΔ:PositivePrefix M x (positiveSimpleLift M z):=by
    obtain ⟨r,hr⟩:=hkc
    refine ⟨r,?_⟩
    rw [←hsc,hr,mul_assoc]
  have hx:x=positiveSimpleLift M (positiveToCoxeter M x):=positivePrefix_of_simple_eq M hxΔ rfl
  refine ⟨positiveToCoxeter M x,?_,?_,?_⟩
  · exact hx ▸ hxb
  · rw [←hx]
    exact ⟨positiveSimpleLift M k,rfl⟩
  · intro w hwa hsw
    obtain ⟨e,he⟩:=hsw
    have hes:e=positiveSimpleLift M (positiveToCoxeter M e):=
      (positive_simple_factors M (positiveGenerator M s) e w he.symm).2
    have heb:PositivePrefix M e b:=by
      obtain ⟨f,hf⟩:=hwa
      refine ⟨f,cancel (positiveGenerator M s) b (e*f) ?_⟩
      rw [←hb,hf,he,mul_assoc]
    have hec:PositivePrefix M e (positiveSimpleLift M c):=by
      have hwΔ:PositivePrefix M (positiveSimpleLift M w) (positiveSimpleLift M z):=
        ⟨positiveSimpleLift M (w⁻¹*z),(positiveSimpleLift_left_complement M z hz w).symm⟩
      obtain ⟨f,hf⟩:=hwΔ
      refine ⟨f,cancel (positiveGenerator M s) (positiveSimpleLift M c) (e*f) ?_⟩
      rw [hsc,hf,he,mul_assoc]
    have heg:PositivePrefix M e (positiveSimpleLift M g):=by
      rw [hes] at heb ⊢
      exact hgreat _ heb
    obtain ⟨r,hr⟩:=hmeet e heg hec
    rw [←hx]
    refine ⟨r,?_⟩
    dsimp [x]
    rw [he,hr,mul_assoc]

theorem positive_greedy_head
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a:PositiveArtin M) : HasPositiveHead M a := by
  induction a using (measure (positiveDegree M)).wf.induction with
  | h a ih=>
    by_cases ha:a=1
    · subst a
      refine ⟨1,by rw [positiveSimpleLift_one];exact positivePrefix_refl M 1,?_⟩
      intro w hw
      rw [positiveSimpleLift_one]
      exact hw
    obtain ⟨l,hl⟩:=positive_word_surjective M a
    cases l with
    | nil=>exact (ha hl.symm).elim
    | cons s ls=>
      have hs:PositivePrefix M (positiveGenerator M s) a:=by rw [←hl];exact positivePrefix_first M s ls
      obtain ⟨h,hh⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) s hs
      refine ⟨h,hh.1,?_⟩
      intro w hwa
      by_cases hw:w=1
      · subst w
        rw [positiveSimpleLift_one]
        exact positivePrefix_one M _
      obtain ⟨t,ht⟩:=exists_simple_prefix M.toCoxeterSystem hw
      have htw:PositivePrefix M (positiveGenerator M t) (positiveSimpleLift M w):=by
        simpa only [positiveSimpleLift_simple] using (positivePrefix_simple_iff M _ _).mpr ht
      have hta:=positivePrefix_trans M htw hwa
      have hlink:=positive_first_letters_connected M z hz a s t hs hta
      have hfront:IsFrontHead M a t h:=by
        clear ht htw hta
        induction hlink with
        | refl=>exact hh
        | @tail t u chain link hi=>
          obtain ⟨d,hda,htd,hud⟩:=link
          obtain ⟨k,hk⟩:=exists_front_head M cancel z hz a (fun b hb=>ih b hb) u
            (positivePrefix_trans M hud hda)
          have hdk:=hk.2.2 d hda hud
          have htk:=positivePrefix_trans M htd hdk
          have hkh:=hi.2.2 k hk.1 htk
          refine ⟨hi.1,positivePrefix_trans M hk.2.1 hkh,?_⟩
          intro v hva huv
          exact positivePrefix_trans M (hk.2.2 v hva huv) hkh
      exact hfront.2.2 w hwa htw

end HarmonicArtin

end OAI
