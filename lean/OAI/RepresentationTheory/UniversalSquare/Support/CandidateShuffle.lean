import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateRotation
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Candidate Shuffle. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidateFirstRowSwap (M b δ : ℕ) (hM : 4 ≤ M) (a c : ℕ)
    (ha : a < M+b+δ) (hc : c < M+b+δ) : Equiv.Perm (candidate M b δ).cells where
  toFun x := ⟨(x.val.1, if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2), by
    rcases x with ⟨⟨i,j⟩,hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    apply mem_candidate.mpr
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega⟩
  invFun x := ⟨(x.val.1, if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2), by
    rcases x with ⟨⟨i,j⟩,hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    apply mem_candidate.mpr
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change (if x.val.1 = 0 then Equiv.swap a c
      (if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2)) = x.val.2
    split_ifs <;> simp
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change (if x.val.1 = 0 then Equiv.swap a c
      (if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap a c x.val.2 else x.val.2)) = x.val.2
    split_ifs <;> simp

def candidateRowShuffle (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidate M b δ).cells :=
  (candidateFirstRowSwap M b δ hM (M+b-1) (M+b+δ-1) (by omega) (by omega)).trans
    (candidateFirstRowSwap M b δ hM (M-1) (M+b-1) (by omega) (by omega))

@[simp] lemma candidateRowShuffle_row (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) : (candidateRowShuffle M b δ hM x).val.1 = x.val.1 := rfl

lemma candidateRowShuffle_triangle (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRowShuffle M b δ hM x).val.1 + (candidateRowShuffle M b δ hM x).val.2 < M-2 ↔
      x.val.1 + x.val.2 < M-2 := by
  change x.val.1 +
    (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)) < M-2 ↔ _
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

def candidateSeparatedRow (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidate M b δ).cells :=
  (candidateRowShuffle M b δ hM).trans (candidateRotateRow M b δ hM)

@[simp] lemma candidateSeparatedRow_row (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) : (candidateSeparatedRow M b δ hM x).val.1 = x.val.1 := rfl

lemma candidateSeparatedRow_mark (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    candidateMark M b (candidateSeparatedRow M b δ hM x).val.2 ↔ x.val.1+x.val.2 < M-2 := by
  change candidateMark M b (candidateRotateRow M b δ hM (candidateRowShuffle M b δ hM x)).val.2 ↔ _
  rw [candidateRotateRow_mark, candidateRowShuffle_triangle]

lemma candidateRotateRow_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRotateRow M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
      else (if x.val.2 < M-2-x.val.1 then x.val.2+2
        else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2) := rfl

lemma candidateRowShuffle_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateRowShuffle M b δ hM x).val.2 =
      if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (Equiv.swap (M+b-1) (M+b+δ-1) x.val.2) else x.val.2 := by
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
        (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)
      else (if x.val.1 = 0 then Equiv.swap (M+b-1) (M+b+δ-1) x.val.2 else x.val.2)) = _
  split_ifs <;> rfl

private lemma separatedFirstRowNumber (M b δ j : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hj : M-2 ≤ j) (hj' : j < M+b+δ) :
    Equiv.swap (M-1) (M+b-1)
      (if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)+2
      else if Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j) < M-2+2 then
        Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)-(M-2)
      else Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)) =
      if j = M-2 then 0 else if j = M+b+δ-1 then 1
      else if j < M+b-1 then j else j+1 := by
  have hs₀ : Equiv.swap (M-1) (M+b-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have ht₀ : Equiv.swap (M+b-1) (M+b+δ-1) (M-2) = M-2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  by_cases hj₀ : j = M-2
  · subst j
    rw [ite_eq_left rfl, ht₀, hs₀, ite_eq_right (by omega), ite_eq_left (by omega), Nat.sub_self]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₀]
  by_cases hj₁ : j = M+b+δ-1
  · subst j
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right, ite_eq_left rfl,
      ite_eq_right (by omega), ite_eq_left (by omega)]
    have he : M-1-(M-2) = 1 := by omega
    rw [he]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [ite_eq_right hj₁]
  let l := Equiv.swap (M-1) (M+b-1) (Equiv.swap (M+b-1) (M+b+δ-1) j)
  have hl : M-2 ≤ l := by
    dsimp only [l]
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have hl₀ : l ≠ M-2 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, hs₀, ht₀] at he'
    exact hj₀ he'
  have hl₁ : l ≠ M-1 := by
    intro he
    have he' := congrArg (fun z => Equiv.swap (M+b-1) (M+b+δ-1) (Equiv.swap (M-1) (M+b-1) z)) he
    simp only [l, Equiv.swap_apply_self, Equiv.swap_apply_left] at he'
    exact hj₁ he'
  change Equiv.swap (M-1) (M+b-1) (if l < M-2 then l+2 else if l < M-2+2 then l-(M-2) else l) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp only [l]
  rw [Equiv.swap_apply_self]
  by_cases he : j = M+b-1
  · subst j
    rw [Equiv.swap_apply_left, ite_eq_right (by omega)]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne he hj₁, ite_eq_left (by omega)]

lemma candidateSeparatedRow_band (M b δ : ℕ) (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    (candidateSeparatedRow M b δ hM x).val.2 =
      if x.val.1 = 0 then
        if x.val.2 = M-2 then 0 else if x.val.2 = M+b+δ-1 then 1
        else if x.val.2 < M+b-1 then x.val.2 else x.val.2+1
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2 := by
  change (candidateRotateRow M b δ hM (candidateRowShuffle M b δ hM x)).val.2 = _
  rw [candidateRotateRow_col, candidateRowShuffle_row, candidateRowShuffle_col]
  have hm := mem_candidate.mp x.property
  rcases x with ⟨⟨i,j⟩,hm0⟩
  dsimp only at *
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, Nat.sub_zero]
    exact separatedFirstRowNumber M b δ j hM hδ (by omega) (by omega)
  · simp only [hi, ite_false]
    rw [ite_eq_right (show ¬j < M-2-i by omega)]

end UniversalTensorSquare
end
end

end OAI
