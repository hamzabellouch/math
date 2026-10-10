import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltListPairDescent

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

def WeakPrefix (a b:W) : Prop := cs.length b=cs.length a+cs.length (a⁻¹*b)

lemma weakPrefix_one (a:W) : WeakPrefix cs 1 a := by simp [WeakPrefix]
lemma weakPrefix_refl (a:W) : WeakPrefix cs a a := by simp [WeakPrefix]
lemma weakPrefix_length {a b:W} (h:WeakPrefix cs a b) : cs.length a≤cs.length b := by
  unfold WeakPrefix at h;omega
lemma weakPrefix_suffix {a b:W} (h:WeakPrefix cs a b) : cs.length (a⁻¹*b)≤cs.length b := by
  unfold WeakPrefix at h;omega

lemma weakPrefix_trans {a b c:W} (hab:WeakPrefix cs a b) (hbc:WeakPrefix cs b c) : WeakPrefix cs a c := by
  have hl:=cs.length_mul_le (a⁻¹*b) (b⁻¹*c)
  have he:(a⁻¹*b)*(b⁻¹*c)=a⁻¹*c:=by group
  rw [he] at hl
  have hr:=cs.length_mul_le a (a⁻¹*c)
  rw [mul_inv_cancel_left] at hr
  unfold WeakPrefix at *
  omega

lemma weakPrefix_antisymm {a b:W} (hab:WeakPrefix cs a b) (hba:WeakPrefix cs b a) : a=b := by
  have hl:=weakPrefix_length cs hba
  have he:cs.length (a⁻¹*b)=0:=by unfold WeakPrefix at hab;omega
  exact inv_mul_eq_one.mp (cs.length_eq_zero_iff.mp he)

lemma weakPrefix_eq_of_length {a b:W} (h:WeakPrefix cs a b) (he:cs.length a=cs.length b) : a=b := by
  have hz:cs.length (a⁻¹*b)=0:=by unfold WeakPrefix at h;omega
  exact inv_mul_eq_one.mp (cs.length_eq_zero_iff.mp hz)

lemma weakPrefix_simple_iff (s:B) (a:W) : WeakPrefix cs (cs.simple s) a ↔ cs.length (cs.simple s*a)+1=cs.length a := by
  simp only [WeakPrefix,cs.length_simple,cs.inv_simple]
  omega

lemma weakPrefix_left_remove {a b:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hb:WeakPrefix cs (cs.simple s) b) :
    WeakPrefix cs (cs.simple s*a) (cs.simple s*b) ↔ WeakPrefix cs a b := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hlb:=(weakPrefix_simple_iff cs s b).mp hb
  have he:(cs.simple s*a)⁻¹*(cs.simple s*b)=a⁻¹*b:=by group
  unfold WeakPrefix
  rw [he]
  omega

lemma weakPrefix_left_add {g a:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hg:WeakPrefix cs g (cs.simple s*a)) :
    WeakPrefix cs (cs.simple s*g) a ∧ cs.length (cs.simple s*g)=cs.length g+1 := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hmul:=cs.length_mul_le (cs.simple s*g) (g⁻¹*(cs.simple s*a))
  have he:(cs.simple s*g)*(g⁻¹*(cs.simple s*a))=a:=by
    rw [mul_assoc,mul_inv_cancel_left,cs.simple_mul_simple_cancel_left]
  rw [he] at hmul
  have hstep:=cs.length_simple_mul g s
  have hlen:cs.length (cs.simple s*g)=cs.length g+1:=by unfold WeakPrefix at hg;omega
  refine ⟨?_,hlen⟩
  have hsuf:(cs.simple s*g)⁻¹*a=g⁻¹*(cs.simple s*a):=by rw [mul_inv_rev,cs.inv_simple,mul_assoc]
  unfold WeakPrefix at *
  rw [hsuf,hlen]
  omega

lemma exists_simple_prefix {a:W} (ha:a≠1) : ∃s:B,WeakPrefix cs (cs.simple s) a := by
  obtain ⟨w,hw,he⟩:=cs.exists_isReduced a
  cases w with
  | nil=>simp only [cs.wordProd_nil] at he;exact (ha he).elim
  | cons s w=>
    refine ⟨s,(weakPrefix_simple_iff cs s a).mpr ?_⟩
    have hl:=hw.drop 1
    simp only [List.drop_succ_cons,List.drop_zero] at hl
    rw [he,hw.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hl.eq]
    rfl

lemma weakPrefix_first_of_reduced (s:B) (w:List B) (h:cs.IsReduced (s::w)) :
    WeakPrefix cs (cs.simple s) (cs.wordProd (s::w)) := by
  apply (weakPrefix_simple_iff cs s _).mpr
  have hr:=h.drop 1
  simp only [List.drop_succ_cons,List.drop_zero] at hr
  rw [h.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hr.eq]
  rfl

variable [Fintype B]

lemma simple_pair_prefix (s t:B) (hne:s≠t) {a:W}
    (hs:WeakPrefix cs (cs.simple s) a) (ht:WeakPrefix cs (cs.simple t) a) :
    WeakPrefix cs (cs.wordProd (altList s t (M s t))) a ∧
      WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t))) ∧
      WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t))) := by
  have hsl:=(weakPrefix_simple_iff cs s a).mp hs
  have htl:=(weakPrefix_simple_iff cs t a).mp ht
  obtain ⟨v,hm,hl,he,he'⟩:=double_descent_prefix cs s t hne a (by omega) (by omega)
  let d:=cs.wordProd (altList s t (M s t))
  have hred:cs.IsReduced (altList s t (M s t)):=by
    have hd:=cs.length_wordProd_le (altList s t (M s t))
    have hh:=cs.length_mul_le d v
    change cs.length (cs.wordProd (altList s t (M s t))*v)≤cs.length (cs.wordProd (altList s t (M s t)))+cs.length v at hh
    rw [←he] at hh
    simp only [length_altList] at hd
    change cs.length d=(altList s t (M s t)).length
    rw [length_altList]
    dsimp [d]
    omega
  have hda:WeakPrefix cs d a:=by
    unfold WeakPrefix
    rw [he,inv_mul_cancel_left,hred.eq,length_altList]
    simpa only [he] using hl
  have hsD:WeakPrefix cs (cs.simple s) d:=by
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    change WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t)))
    rw [hn,altList_succ] at hred ⊢
    exact weakPrefix_first_of_reduced cs s _ hred
  have htD:WeakPrefix cs (cs.simple t) d:=by
    have hdEq:cs.wordProd (altList s t (M s t))=cs.wordProd (altList t s (M s t)):=altList_braid cs s t
    have htred:cs.IsReduced (altList t s (M s t)):=by
      change cs.length (cs.wordProd (altList t s (M s t)))=(altList t s (M s t)).length
      rw [←hdEq,hred.eq,length_altList,length_altList]
    change WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t)))
    rw [hdEq]
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    rw [hn,altList_succ] at htred ⊢
    exact weakPrefix_first_of_reduced cs t _ htred
  exact ⟨hda,hsD,htD⟩

end HarmonicArtin.CoxeterExchange

end OAI
