import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveHead

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma positivePrefix_mul_left (c:PositiveArtin M) {a b:PositiveArtin M} (h:PositivePrefix M a b) :
    PositivePrefix M (c*a) (c*b) := by
  obtain ⟨r,hr⟩:=h
  exact ⟨r,by rw [hr,mul_assoc]⟩

omit [Fintype S] in
lemma positivePrefix_mul_left_iff (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (c a b:PositiveArtin M) : PositivePrefix M (c*a) (c*b) ↔ PositivePrefix M a b := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,cancel c b (a*r) (by simpa only [mul_assoc] using hr)⟩
  · exact positivePrefix_mul_left M c

omit [Fintype S] in
lemma exists_positive_first {a:PositiveArtin M} (ha:a≠1) :
    ∃s:S,PositivePrefix M (positiveGenerator M s) a := by
  obtain ⟨w,hw⟩:=positive_word_surjective M a
  cases w with
  | nil=>exact (ha hw.symm).elim
  | cons s w=>exact ⟨s,hw ▸ positivePrefix_first M s w⟩

lemma positive_common_atoms_prefix
    (heads:∀a:PositiveArtin M,HasPositiveHead M a)
    (a b:PositiveArtin M) (s t:S)
    (hsa:PositivePrefix M (positiveGenerator M s) a)
    (hsb:PositivePrefix M (positiveGenerator M s) b)
    (hta:PositivePrefix M (positiveGenerator M t) a)
    (htb:PositivePrefix M (positiveGenerator M t) b) :
    ∃d:PositiveArtin M,PositivePrefix M d a ∧ PositivePrefix M d b ∧
      PositivePrefix M (positiveGenerator M s) d ∧ PositivePrefix M (positiveGenerator M t) d := by
  obtain ⟨u,hua,hU⟩:=heads a
  obtain ⟨v,hvb,hV⟩:=heads b
  obtain ⟨d,hdu,hdv,hd⟩:=exists_greatest_common_simplePrefix M u v
  refine ⟨positiveSimpleLift M d,positivePrefix_trans M hdu hua,positivePrefix_trans M hdv hvb,?_,?_⟩
  · simpa only [positiveSimpleLift_simple] using hd (positiveSimpleLift M (M.toCoxeterSystem.simple s)) (hU (M.toCoxeterSystem.simple s) (by simpa only [positiveSimpleLift_simple] using hsa))
      (hV (M.toCoxeterSystem.simple s) (by simpa only [positiveSimpleLift_simple] using hsb))
  · simpa only [positiveSimpleLift_simple] using hd (positiveSimpleLift M (M.toCoxeterSystem.simple t)) (hU (M.toCoxeterSystem.simple t) (by simpa only [positiveSimpleLift_simple] using hta))
      (hV (M.toCoxeterSystem.simple t) (by simpa only [positiveSimpleLift_simple] using htb))

omit [Fintype S] in
lemma positive_common_maximal_remove (c a b g:PositiveArtin M)
    (hmax:∀x:PositiveArtin M,PositivePrefix M x (c*a)→PositivePrefix M x (c*b)→positiveDegree M x≤positiveDegree M (c*g)) :
    ∀x:PositiveArtin M,PositivePrefix M x a→PositivePrefix M x b→positiveDegree M x≤positiveDegree M g := by
  intro x hxa hxb
  have hh:=hmax (c*x) (positivePrefix_mul_left M c hxa) (positivePrefix_mul_left M c hxb)
  simp only [positiveDegree_mul] at hh
  omega

theorem maximal_common_positivePrefix_greatest
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (heads:∀a:PositiveArtin M,HasPositiveHead M a)
    (a b g:PositiveArtin M)
    (hga:PositivePrefix M g a) (hgb:PositivePrefix M g b)
    (hmax:∀x:PositiveArtin M,PositivePrefix M x a→PositivePrefix M x b→positiveDegree M x≤positiveDegree M g) :
    ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g := by
  induction a using (measure (positiveDegree M)).wf.induction generalizing b g with
  | h a ih=>
    intro e hea heb
    by_cases he:e=1
    · rw [he];exact positivePrefix_one M g
    obtain ⟨s,hse⟩:=exists_positive_first M he
    have hsa:=positivePrefix_trans M hse hea
    have hsb:=positivePrefix_trans M hse heb
    have hsg:PositivePrefix M (positiveGenerator M s) g:=by
      have hg:g≠1:=by
        intro hg
        have hh:=hmax _ hsa hsb
        rw [hg,positiveDegree_one,positiveDegree_generator] at hh
        omega
      obtain ⟨t,htg⟩:=exists_positive_first M hg
      have hta:=positivePrefix_trans M htg hga
      have htb:=positivePrefix_trans M htg hgb
      obtain ⟨d,hda,hdb,hsd,htd⟩:=positive_common_atoms_prefix M heads a b s t hsa hsb hta htb
      obtain ⟨a',ha'⟩:=hta
      obtain ⟨b',hb'⟩:=htb
      obtain ⟨g',hg'⟩:=htg
      obtain ⟨d',hd'⟩:=htd
      have Hga:PositivePrefix M g' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hg'];exact hga)
      have Hgb:PositivePrefix M g' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hg'];exact hgb)
      have Hda:PositivePrefix M d' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hd'];exact hda)
      have Hdb:PositivePrefix M d' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hd'];exact hdb)
      have Hmax:=positive_common_maximal_remove M (positiveGenerator M t) a' b' g' (by rw [←ha',←hb',←hg'];exact hmax)
      have hlt:positiveDegree M a'<positiveDegree M a:=by rw [ha',positiveDegree_mul,positiveDegree_generator];omega
      have hdg:=positivePrefix_mul_left M (positiveGenerator M t) (ih a' hlt b' g' Hga Hgb Hmax d' Hda Hdb)
      rw [←hd',←hg'] at hdg
      exact positivePrefix_trans M hsd hdg
    obtain ⟨a',ha'⟩:=hsa
    obtain ⟨b',hb'⟩:=hsb
    obtain ⟨g',hg'⟩:=hsg
    obtain ⟨e',he'⟩:=hse
    have Hga:PositivePrefix M g' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←hg'];exact hga)
    have Hgb:PositivePrefix M g' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←hg'];exact hgb)
    have Hea:PositivePrefix M e' a':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←ha',←he'];exact hea)
    have Heb:PositivePrefix M e' b':=(positivePrefix_mul_left_iff M cancel _ _ _).mp (by rw [←hb',←he'];exact heb)
    have Hmax:=positive_common_maximal_remove M (positiveGenerator M s) a' b' g' (by rw [←ha',←hb',←hg'];exact hmax)
    have hlt:positiveDegree M a'<positiveDegree M a:=by rw [ha',positiveDegree_mul,positiveDegree_generator];omega
    have heg:=positivePrefix_mul_left M (positiveGenerator M s) (ih a' hlt b' g' Hga Hgb Hmax e' Hea Heb)
    rwa [←he',←hg'] at heg

theorem positive_greatest_common_left_divisor
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c)
    (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (a b:PositiveArtin M) :
    ∃g:PositiveArtin M,PositivePrefix M g a ∧ PositivePrefix M g b ∧
      ∀e:PositiveArtin M,PositivePrefix M e a→PositivePrefix M e b→PositivePrefix M e g := by
  let P:ℕ→Prop:=fun n=>∃g:PositiveArtin M,PositivePrefix M g a ∧ PositivePrefix M g b ∧ positiveDegree M g=n
  have hP:P 0:=⟨1,positivePrefix_one M a,positivePrefix_one M b,positiveDegree_one M⟩
  obtain ⟨g,hga,hgb,hlen⟩:=Nat.findGreatest_spec (Nat.zero_le (positiveDegree M a)) hP
  refine ⟨g,hga,hgb,maximal_common_positivePrefix_greatest M cancel (positive_greedy_head M cancel z hz) a b g hga hgb ?_⟩
  intro x hxa hxb
  rw [hlen]
  exact Nat.le_findGreatest (positivePrefix_degree M hxa) ⟨x,hxa,hxb,rfl⟩

end HarmonicArtin

end OAI
