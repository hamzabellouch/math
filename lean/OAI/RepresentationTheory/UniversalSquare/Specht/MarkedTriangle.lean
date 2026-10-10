import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Candidate
import OAI.RepresentationTheory.UniversalSquare.Support.AttachmentTransfer

namespace OAI

/-! Marked Triangle. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

def candidateMark (M b j : ℕ) : Prop :=
  (2 ≤ j ∧ j < M - 1) ∨ j = M + b - 1

def markedRowEquiv (M b δ : ℕ) (hM : 4 ≤ M) :
    {x : (candidate M b δ).cells // candidateMark M b x.val.2} ≃
      (staircase (M-2)).cells where
  toFun x := ⟨(x.val.val.1, if x.val.val.2 = M+b-1 then M-3 else x.val.val.2-2), by
    rcases x with ⟨⟨⟨i,j⟩, hx⟩, hm⟩
    have hx := mem_candidate.mp hx
    simp only [candidateMark] at hm
    apply mem_staircase.mpr
    dsimp only at *
    split_ifs <;> omega⟩
  invFun x := ⟨⟨(x.val.1, if x.val.2 = M-3 then M+b-1 else x.val.2+2), by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_staircase.mp hx
    apply mem_candidate.mpr
    dsimp only at *
    split_ifs <;> omega⟩, by
      rcases x with ⟨⟨i,j⟩, hx⟩
      have hx := mem_staircase.mp hx
      dsimp [candidateMark] at *
      split_ifs <;> omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rcases x with ⟨⟨⟨i,j⟩, hx⟩, hm⟩
    have hx := mem_candidate.mp hx
    dsimp [candidateMark] at hm
    dsimp only at *
    apply Prod.ext
    · rfl
    · dsimp; split_ifs <;> omega
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_staircase.mp hx
    dsimp only at *
    apply Prod.ext
    · rfl
    · dsimp; split_ifs <;> omega

def markedColEquiv (M b δ : ℕ) (hM : 4 ≤ M) :
    {x : (candidate M b δ).cells // candidateMark M b x.val.1} ≃
      (staircase (M-2)).cells where
  toFun x := ⟨(if x.val.val.1 = M+b-1 then M-3 else x.val.val.1-2, x.val.val.2), by
    rcases x with ⟨⟨⟨i,j⟩, hx⟩, hm⟩
    have hx := mem_candidate.mp hx
    simp only [candidateMark] at hm
    apply mem_staircase.mpr
    dsimp only at *
    split_ifs <;> omega⟩
  invFun x := ⟨⟨(if x.val.1 = M-3 then M+b-1 else x.val.1+2, x.val.2), by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_staircase.mp hx
    apply mem_candidate.mpr
    dsimp only at *
    split_ifs <;> omega⟩, by
      rcases x with ⟨⟨i,j⟩, hx⟩
      have hx := mem_staircase.mp hx
      dsimp [candidateMark] at *
      split_ifs <;> omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rcases x with ⟨⟨⟨i,j⟩, hx⟩, hm⟩
    have hx := mem_candidate.mp hx
    dsimp [candidateMark] at hm
    dsimp only at *
    apply Prod.ext
    · dsimp; split_ifs <;> omega
    · rfl
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_staircase.mp hx
    dsimp only at *
    apply Prod.ext
    · dsimp; split_ifs <;> omega
    · rfl

theorem candidate_marked_rigidity (M b δ : ℕ) (hM : 4 ≤ M)
    (g k : Equiv.Perm (candidate M b δ).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, candidateMark M b (g x).val.2 ↔ candidateMark M b (k x).val.1) :
    ∀ x, candidateMark M b (g x).val.2 ↔ x.val.1 + x.val.2 < M-2 := by
  classical
  let A : Finset (candidate M b δ).cells :=
    Finset.univ.filter (fun x => candidateMark M b (g x).val.2)
  let B : Finset (candidate M b δ).cells :=
    Finset.univ.filter (fun x => x.val.1 + x.val.2 < M-2)
  let eR : A ≃ (staircase (M-2)).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter,
      Finset.mem_univ, true_and])).trans (markedRowEquiv M b δ hM)
  let eC : A ≃ (staircase (M-2)).cells :=
    (Equiv.subtypeEquiv k (by
      intro x
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hc x)).trans (markedColEquiv M b δ hM)
  let eB : B ≃ (staircase (M-2)).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_candidate.mpr (Or.inl (by
        have hx := mem_staircase.mp x.property; omega))⟩,
        by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, markedRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, markedColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (candidate M b δ).cells =>
    2 * ((M-2 : ℕ) : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < M-2 := by simpa [B] using hx
      dsimp [w]; omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < M-2 := by simpa [B] using hx
      dsimp [w]; omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this

end UniversalTensorSquare

namespace Saxl

def sameMarkProjection (n d e : ℕ) (Q : ℕ → Prop) :
    Representation.IntertwiningMap (wordRep n (d*e)) (wordRep n (d*e)) := by
  classical
  exact {
    toFun z w := if (∀ i, Q (splitLeft w i).val ↔ Q (splitRight w i).val) then z w else 0
    map_add' z y := by ext w; dsimp; split_ifs <;> simp
    map_smul' c z := by ext w; dsimp; split_ifs <;> simp
    isIntertwining' g := by
      apply LinearMap.ext
      intro z
      funext w
      change (if (∀ i, Q (splitLeft w i).val ↔ Q (splitRight w i).val) then z (w ∘ g) else 0) =
        (if (∀ i, Q (splitLeft (w ∘ g) i).val ↔ Q (splitRight (w ∘ g) i).val)
          then z (w ∘ g) else 0)
      congr 1
      apply propext
      exact (g.forall_congr_right).symm }
end Saxl

namespace UniversalTensorSquare
open Saxl

def candidateTriangle {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) (i : Fin n) : Prop :=
  (t i).val.1 + (t i).val.2 < M-2

theorem candidate_projected_marked_positions {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin n → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) w ≠ 0) :
    ∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i := by
  classical
  have heq : ∀ i, candidateMark M b (splitLeft w i).val ↔
      candidateMark M b (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameMarkProjection, hh]
  have hww : rowColumnWord t w ≠ 0 := by
    simpa [sameMarkProjection, heq] using hw
  have hp : polytabloid (transposeTableau t) (splitLeft w) *
      polytabloid t (splitRight w) ≠ 0 := by
    simpa only [rowColumnWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (transposeTableau t) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support t _ (mul_ne_zero_iff.mp hp).2
  let gc : Equiv.Perm (candidate M b δ).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (candidate M b δ).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, candidateMark M b (gc x).val.2 ↔ candidateMark M b (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := candidate_marked_rigidity M b δ hM gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, rowWord, transposeTableau, candidateTriangle] using hh

theorem candidate_projected_sector {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      coordinateProjection (fun w =>
        (∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i) ∧
        (∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i))
        (rowColumnWord t) := by
  classical
  ext w
  by_cases he : ∀ i, candidateMark M b (splitLeft w i).val ↔
      candidateMark M b (splitRight w i).val
  · by_cases hw : sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) w = 0
    · have hw' : rowColumnWord t w = 0 := by simpa [sameMarkProjection, he] using hw
      simp [hw, hw']
    · have hD := candidate_projected_marked_positions hM t w hw
      have hD' : ∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i :=
        fun i => (he i).symm.trans (hD i)
      simp [sameMarkProjection, he, hD']
  · have hn : ¬ ((∀ i, candidateMark M b (splitLeft w i).val ↔ candidateTriangle t i) ∧
        (∀ i, candidateMark M b (splitRight w i).val ↔ candidateTriangle t i)) := by
      rintro ⟨h₁,h₂⟩
      exact he (fun i => (h₁ i).trans (h₂ i).symm)
    simp [sameMarkProjection, he, hn]

end UniversalTensorSquare
end
end

end OAI
