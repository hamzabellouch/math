import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.WordContents

namespace OAI

/-! Part Words. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

theorem exists_word_of_parts (ps : List ℕ) {n : ℕ} (hn : ps.sum = n) :
    ∃ w : Fin n → Fin ps.length, ∀ j, wordContent w j = ps.get j := by
  classical
  have hc : Fintype.card (Σ j : Fin ps.length, Fin (ps.get j)) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← List.sum_ofFn, List.ofFn_get, hn]
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i).1, fun j => ?_⟩
  rw [wordContent,Finset.card_filter,← Equiv.sum_comp e,Fintype.sum_sigma]
  simp

def balancedParts (n k : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin k => n/k + if j.val < n%k then 1 else 0)

@[simp] lemma balancedParts_length (n k : ℕ) : (balancedParts n k).length = k :=
  List.length_ofFn

lemma balancedParts_part {n k p : ℕ} (hp : p ∈ balancedParts n k) :
    n/k ≤ p ∧ p ≤ (n+k-1)/k := by
  simp only [balancedParts, List.mem_ofFn] at hp
  obtain ⟨j,rfl⟩ := hp
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  have hn : n = k*(n/k) + n%k := (Nat.div_add_mod n k).symm
  have hr := Nat.mod_lt n hk
  constructor
  · omega
  · split_ifs with h
    · apply (Nat.le_div_iff_mul_le hk).mpr
      have ht : n%k ≥ 1 := by omega
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm]
      omega
    · apply (Nat.le_div_iff_mul_le hk).mpr
      simp only [Nat.add_zero]
      rw [Nat.mul_comm]
      omega

lemma balancedParts_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    ∀ p ∈ balancedParts n k, 0 < p := by
  intro p hp
  have h := (balancedParts_part hp).1
  have hn : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa)
  omega

lemma balancedParts_sum (n k : ℕ) (hk : 0 < k) : (balancedParts n k).sum = n := by
  classical
  rw [balancedParts,List.sum_ofFn,Finset.sum_add_distrib]
  have hc : (∑ j : Fin k, if j.val < n%k then 1 else 0) = n%k := by
    rw [← Finset.card_filter]
    have he : Finset.univ.filter (fun j : Fin k => j.val < n%k) =
        Finset.Iio ⟨n%k,Nat.mod_lt n hk⟩ := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,Fin.lt_def]
    rw [he]
    simp
  rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact Nat.div_add_mod n k

end Saxl
end
end

end OAI
