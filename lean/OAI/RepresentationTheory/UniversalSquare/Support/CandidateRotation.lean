import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.MarkedTriangle

namespace OAI

/-! Candidate Rotation. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidateBaseRotateCell (M b δ : ℕ) (x : (candidate M b δ).cells) :
    (candidate M b δ).cells :=
  ⟨(x.val.1,
      if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1)
      else x.val.2), by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    apply mem_candidate.mpr
    split_ifs <;> omega⟩

lemma candidateBaseRotateCell_injective (M b δ : ℕ) :
    Function.Injective (candidateBaseRotateCell M b δ) := by
  intro x y he
  have hi0 := congrArg (fun z : (candidate M b δ).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (candidate M b δ).cells => z.val.2) he
  dsimp only [candidateBaseRotateCell] at hj
  rw [hi] at hj
  apply Subtype.ext
  apply Prod.ext hi
  split_ifs at hj <;> omega

def candidateLastSwapCell (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) : (candidate M b δ).cells :=
  ⟨(x.val.1, if x.val.1 = 0 then (Equiv.swap (M-1) (M+b-1)) x.val.2 else x.val.2), by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    apply mem_candidate.mpr
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega⟩

lemma candidateLastSwapCell_injective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidateLastSwapCell M b δ hM) := by
  intro x y he
  have hi0 := congrArg (fun z : (candidate M b δ).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (candidate M b δ).cells => z.val.2) he
  dsimp only [candidateLastSwapCell] at hj
  rw [hi] at hj
  apply Subtype.ext
  apply Prod.ext hi
  by_cases h : y.val.1 = 0
  · simp only [h, ite_true] at hj
    exact (Equiv.swap _ _).injective hj
  · simpa only [h, ite_false] using hj

def candidateRotateRow (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidate M b δ).cells :=
  Equiv.ofBijective (candidateLastSwapCell M b δ hM ∘ candidateBaseRotateCell M b δ)
    ⟨(candidateLastSwapCell_injective M b δ hM).comp (candidateBaseRotateCell_injective M b δ),
      Finite.surjective_of_injective
        ((candidateLastSwapCell_injective M b δ hM).comp (candidateBaseRotateCell_injective M b δ))⟩

@[simp] lemma candidateRotateRow_row (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) : (candidateRotateRow M b δ hM x).val.1 = x.val.1 := rfl

lemma candidateRotateRow_mark (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    candidateMark M b (candidateRotateRow M b δ hM x).val.2 ↔
      x.val.1 + x.val.2 < M-2 := by
  have hx := mem_candidate.mp x.property
  change candidateMark M b
    (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) ↔ _
  rcases x with ⟨⟨i,j⟩, hx0⟩
  dsimp only at *
  simp only [candidateMark, Equiv.swap_apply_def]
  split_ifs <;> omega

def candidateSwap (M b δ : ℕ) : Equiv.Perm (candidate M b δ).cells where
  toFun x := ⟨x.val.swap, by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    exact mem_candidate.mpr (by dsimp; omega)⟩
  invFun x := ⟨x.val.swap, by
    rcases x with ⟨⟨i,j⟩, hx⟩
    have hx := mem_candidate.mp hx
    dsimp only at *
    exact mem_candidate.mpr (by dsimp; omega)⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap _
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap _

def candidateRotateCol (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidate M b δ).cells :=
  ((candidateSwap M b δ).trans (candidateRotateRow M b δ hM)).trans (candidateSwap M b δ)

@[simp] lemma candidateRotateCol_col (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) : (candidateRotateCol M b δ hM x).val.2 = x.val.2 := rfl

lemma candidateRotateCol_mark (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    candidateMark M b (candidateRotateCol M b δ hM x).val.1 ↔
      x.val.1 + x.val.2 < M-2 := by
  have hh := candidateRotateRow_mark M b δ hM (candidateSwap M b δ x)
  change candidateMark M b (candidateRotateRow M b δ hM (candidateSwap M b δ x)).val.2 ↔ _
  simpa [candidateSwap, Nat.add_comm] using hh

def candidateRotateRowPositions {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) : columnGroup (transposeTableau t) :=
  ⟨(t.trans (candidateRotateRow M b δ hM)).trans t.symm, by
    intro i
    change (t (t.symm (candidateRotateRow M b δ hM (t i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def candidateRotateColPositions {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) : columnGroup t :=
  ⟨(t.trans (candidateRotateCol M b δ hM)).trans t.symm, by
    intro i
    change (t (t.symm (candidateRotateCol M b δ hM (t i)))).val.2 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

theorem candidate_projected_ne_zero {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) ≠ 0 := by
  classical
  let a := rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm _)
  let c := rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm _)
  let w := mergeWords a c
  have ha i : candidateMark M b (a i).val ↔ candidateTriangle t i := by
    have hh := candidateRotateRow_mark M b δ hM (t i)
    simpa [a, rowWord, transposeTableau, candidateRotateRowPositions, candidateTriangle] using hh
  have hc i : candidateMark M b (c i).val ↔ candidateTriangle t i := by
    have hh := candidateRotateCol_mark M b δ hM (t i)
    simpa [c, rowWord, candidateRotateColPositions, candidateTriangle] using hh
  intro hz
  have he := congrFun hz w
  change sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) w = 0 at he
  simp only [sameMarkProjection, Representation.IntertwiningMap.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, rowColumnWord, wordTensor_tmul, w, splitLeft_merge, splitRight_merge,
    a, c, polytabloid_column_coeff] at he
  have hn (g : Equiv.Perm (Fin n)) : signC g ≠ 0 := by
    intro hz
    have hh := signC_mul_self g
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hpac : ∀ i, candidateMark M b (a i).val ↔ candidateMark M b (c i).val :=
    fun i => (ha i).trans (hc i).symm
  rw [ite_eq_left hpac] at he
  exact mul_ne_zero (hn _) (hn _) he

end UniversalTensorSquare
end
end

end OAI
