import Mathlib
import OAI.RepresentationTheory.Saxl.Basic

namespace OAI

/-! Parity-compatible triangular degrees and remainder bounds. -/

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquares

def triangular (m : ℕ) : ℕ := m * (m + 1) / 2

lemma triangular_eq_staircase_card (m : ℕ) : triangular m = (Saxl.staircase m).card :=
  (Saxl.staircase_card m).symm

@[simp] lemma triangular_zero : triangular 0 = 0 := rfl
@[simp] lemma triangular_one : triangular 1 = 1 := rfl

lemma triangular_succ (m : ℕ) : triangular (m + 1) = triangular m + m + 1 := by
  simpa only [triangular_eq_staircase_card, Nat.add_assoc] using Saxl.staircase_card_succ m

lemma index_le_triangular (m : ℕ) : m ≤ triangular m := by
  induction m with
  | zero => simp
  | succ m ih => rw [triangular_succ]; omega

lemma triangular_add_three (m : ℕ) : triangular (m + 3) = triangular m + 3 * m + 6 := by
  have h1 := triangular_succ m
  have h2 := triangular_succ (m + 1)
  have h3 := triangular_succ (m + 2)
  norm_num [Nat.add_assoc] at h1 h2 h3
  omega

def largestIndex (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => triangular m ≤ n ∧ triangular m % 2 = n % 2) n

lemma largestIndex_spec (n : ℕ) :
    triangular (largestIndex n) ≤ n ∧ triangular (largestIndex n) % 2 = n % 2 := by
  unfold largestIndex
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · apply Nat.findGreatest_spec (P := fun m => triangular m ≤ n ∧ triangular m % 2 = n % 2) (m := 0) (Nat.zero_le n)
    exact ⟨by simp, by simpa using hn.symm⟩
  · have h1 : 1 ≤ n := by omega
    apply Nat.findGreatest_spec (P := fun m => triangular m ≤ n ∧ triangular m % 2 = n % 2) (m := 1) h1
    exact ⟨by simpa using h1, by simpa using hn.symm⟩

lemma largestIndex_maximal {n m : ℕ} (hmn : triangular m ≤ n)
    (hp : triangular m % 2 = n % 2) : m ≤ largestIndex n :=
  Nat.le_findGreatest ((index_le_triangular m).trans hmn) ⟨hmn, hp⟩

def remainderPairs (n : ℕ) : ℕ := (n - triangular (largestIndex n)) / 2

lemma degree_decomposition (n : ℕ) :
    triangular (largestIndex n) + 2 * remainderPairs n = n := by
  have h := largestIndex_spec n
  unfold remainderPairs
  omega

lemma odd_index_remainder_bound (n : ℕ) (hodd : largestIndex n % 2 = 1) :
    2 * remainderPairs n ≤ largestIndex n - 1 := by
  have hs := (largestIndex_spec n).2
  have ht := triangular_succ (largestIndex n)
  have hp : triangular (largestIndex n + 1) % 2 = n % 2 := by omega
  have hn : n < triangular (largestIndex n + 1) := by
    by_contra h
    have hmax := largestIndex_maximal (Nat.ge_of_not_lt h) hp
    omega
  have hd := degree_decomposition n
  omega

lemma even_index_remainder_bound (n : ℕ) (heven : largestIndex n % 2 = 0) :
    2 * remainderPairs n ≤ 3 * largestIndex n + 4 := by
  have hs := (largestIndex_spec n).2
  have ht := triangular_add_three (largestIndex n)
  have hp : triangular (largestIndex n + 3) % 2 = n % 2 := by omega
  have hn : n < triangular (largestIndex n + 3) := by
    by_contra h
    have hmax := largestIndex_maximal (Nat.ge_of_not_lt h) hp
    omega
  have hd := degree_decomposition n
  omega

lemma small_index_degree_bound (n : ℕ) (hsmall : largestIndex n < 9) : n ≤ 64 := by
  by_contra hn
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have h66 : 66 ≤ n := by omega
    have hmax : 11 ≤ largestIndex n := largestIndex_maximal
      (by norm_num [triangular]; exact h66)
      (by norm_num [triangular]; exact heven.symm)
    omega
  · have h45 : 45 ≤ n := by omega
    have hmax : 9 ≤ largestIndex n := largestIndex_maximal
      (by norm_num [triangular]; exact h45)
      (by norm_num [triangular]; exact hodd.symm)
    omega
end UniversalTensorSquares


end

end OAI
