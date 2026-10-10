import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def altList (i j : B) : ℕ → List B
  | 0 => []
  | n+1 => i :: altList j i n

@[simp] lemma altList_zero (i j : B) : altList i j 0 = [] := rfl
@[simp] lemma altList_succ (i j : B) (n : ℕ) : altList i j (n+1) = i::altList j i n := rfl
@[simp] lemma length_altList (i j : B) (n : ℕ) : (altList i j n).length = n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp [ih]

lemma altList_reverse (i j : B) (n : ℕ) :
    altList i j n = (CoxeterSystem.alternatingWord j i n).reverse := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => rw [altList_succ, CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_append, List.reverse_singleton, ih, List.singleton_append]

lemma take_altList (i j : B) (n k : ℕ) (hk : k ≤ n) :
    (altList i j n).take k = altList i j k := by
  induction k generalizing i j n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n => simp only [altList_succ, List.take_succ_cons, ih j i n (by omega)]

lemma mem_altList (i j : B) (n : ℕ) : ∀ k ∈ altList i j n, k ∈ ({i,j} : Set B) := by
  induction n generalizing i j with
  | zero => simp
  | succ n ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simp
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using ih j i k hk

lemma reduced_not_double (i : B) (u : List B) : ¬ cs.IsReduced (i::i::u) := by
  intro h
  have hb := cs.length_wordProd_le u
  have he := h.eq
  simp only [cs.wordProd_cons, ← mul_assoc, cs.simple_mul_simple_self, one_mul,
    List.length_cons] at he
  omega

lemma reduced_pair_cons_eq_alt (i j : B) (u : List B) (hu : cs.IsReduced (i::u))
    (hJ : ∀ k ∈ u, k ∈ ({i,j} : Set B)) : i::u = altList i j (u.length+1) := by
  induction u generalizing i j with
  | nil => rfl
  | cons k u ih =>
    have hk := hJ k (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with hk | hk
    · subst k
      exact (reduced_not_double cs i u hu).elim
    · subst k
      rw [List.length_cons, altList_succ]
      congr 1
      apply ih j i
      · simpa only [List.drop_succ_cons, List.drop_zero] using hu.drop 1
      · intro k hk
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using
          hJ k (List.mem_cons_of_mem j hk)

lemma wordProd_altList_even (i j : B) (n : ℕ) :
    cs.wordProd (altList i j (2*n)) = (cs.simple i*cs.simple j)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, altList_succ, altList_succ,
      cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    simp only [mul_assoc]

lemma wordProd_altList_odd (i j : B) (n : ℕ) :
    cs.wordProd (altList i j (2*n+1)) = (cs.simple i*cs.simple j)^n * cs.simple i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega, altList_succ, altList_succ,
      cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    simp only [mul_assoc]

lemma wordProd_altList_difference (i j : B) (n : ℕ) :
    cs.wordProd (altList i j n) * (cs.wordProd (altList j i n))⁻¹ =
      (cs.simple i*cs.simple j)^n := by
  rcases Nat.even_or_odd' n with ⟨k,rfl | rfl⟩
  · rw [wordProd_altList_even, wordProd_altList_even, ← inv_pow]
    simp only [mul_inv_rev, cs.inv_simple]
    rw [← pow_add]
    congr 1
    omega
  · rw [wordProd_altList_odd, wordProd_altList_odd, mul_inv_rev, cs.inv_simple,
      ← inv_pow]
    simp only [mul_inv_rev, cs.inv_simple]
    calc
      _ = (cs.simple i*cs.simple j)^k * (cs.simple i*cs.simple j) *
          (cs.simple i*cs.simple j)^k := by group
      _ = _ := by rw [← pow_succ, ← pow_add]; congr 1; omega

lemma altList_braid (i j : B) :
    cs.wordProd (altList i j (M i j)) = cs.wordProd (altList j i (M i j)) := by
  rw [altList_reverse, altList_reverse, cs.wordProd_reverse, cs.wordProd_reverse]
  apply congrArg Inv.inv
  simpa only [CoxeterSystem.braidWord, ← M.symmetric i j] using cs.wordProd_braidWord_eq j i

lemma reduced_altList_le (i j : B) (n : ℕ) (hm : 2 ≤ M i j)
    (hn : cs.IsReduced (altList i j n)) : n ≤ M i j := by
  by_contra! hlt
  have hr := hn.take (M i j+1)
  rw [take_altList i j n (M i j+1) (by omega)] at hr
  have he : cs.wordProd (altList i j (M i j+1)) =
      cs.wordProd (altList j i (M i j-1)) := by
    rw [altList_reverse, altList_reverse, cs.wordProd_reverse, cs.wordProd_reverse]
    apply congrArg Inv.inv
    have ht := cs.prod_alternatingWord_eq_prod_alternatingWord_sub j i (M i j+1)
      (by rw [← M.symmetric i j]; omega)
    rw [← M.symmetric i j, show M i j*2-(M i j+1)=M i j-1 by omega] at ht
    exact ht
  have hb := cs.length_wordProd_le (altList j i (M i j-1))
  rw [← he, hr.eq, length_altList, length_altList] at hb
  omega

end HarmonicArtin.CoxeterExchange

end OAI
