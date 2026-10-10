import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandSplit

namespace OAI

/-! Band Groups. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidatePartsSwap {M b δ : ℕ} : CandidateBandParts M b δ → CandidateBandParts M b δ
  | .inl q => .inl q.rev
  | .inr (.inl x) => .inr (.inr x)
  | .inr (.inr x) => .inr (.inl x)

lemma candidatePartsCell_swap {M b δ : ℕ} (hM : 4 ≤ M) (x : CandidateBandParts M b δ) :
    (candidatePartsCell M b δ hM (candidatePartsSwap x)).val.val =
      (candidatePartsCell M b δ hM x).val.val.swap := by
  rcases x with q | (z | z)
  · exact (candidatePathCell_swap hM q).symm
  · rfl
  · exact Prod.swap_swap _ |>.symm

lemma candidateParts_col_sectors {M b δ : ℕ} (hM : 4 ≤ M)
    (x y : CandidateBandParts M b δ)
    (hcol : (candidatePartsCell M b δ hM x).val.val.2 =
      (candidatePartsCell M b δ hM y).val.val.2) :
    (Sum.isLeft x = true ↔ Sum.isLeft y = true) ↔
      ((candidatePartsCell M b δ hM x).val.val.swap ∈ attachmentNE M b δ ↔
        (candidatePartsCell M b δ hM y).val.val.swap ∈ attachmentNE M b δ) := by
  have H := candidateParts_row_sectors hM (candidatePartsSwap x) (candidatePartsSwap y)
    (by simpa only [candidatePartsCell_swap, Prod.fst_swap] using hcol)
  rw [candidatePartsCell_swap, candidatePartsCell_swap] at H
  have he (z : CandidateBandParts M b δ) : (candidatePartsSwap z).isLeft = z.isLeft := by
    rcases z with z | (z | z) <;> rfl
  simpa only [he] using H

lemma candidateBandCol_sector_eq {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
      sectorGroup (fun i => (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) =
    fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
      sectorGroup (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) := by
  apply Subgroup.ext
  intro g
  change ((∀ i, (candidateBandTableau t (g i)).val.2 = (candidateBandTableau t i).val.2) ∧ _) ↔
    ((∀ i, (candidateBandTableau t (g i)).val.2 = (candidateBandTableau t i).val.2) ∧ _)
  apply and_congr_right
  intro hg
  change (∀ i, _ ↔ _) ↔ (∀ i, _ ↔ _)
  apply forall_congr'
  intro i
  let E := candidateBandPartsEquiv hM t s₁ s₂
  let f := Equiv.sumCongr (Equiv.refl (Fin (2*M-1))) (Equiv.sumCongr s₁ s₂)
  have H (i) : (candidateBandTableau t i).val =
      (candidatePartsCell M b δ hM (f (E i))).val.val := by
    rw [← candidateBandParts_cell hM t s₁ s₂, Equiv.symm_apply_apply]
  have hh := candidateParts_col_sectors hM (f (E (g i))) (f (E i)) (by
    rw [← H, ← H]; exact hg i)
  dsimp only at *
  simp_rw [H]
  have hside (j) : (f (E j)).isLeft = ((candidateBandSplit hM t s₁ s₂) j).isLeft := by
    dsimp only [candidateBandSplit, Equiv.trans_apply, f]
    cases E j <;> rfl
  rw [hside, hside] at hh
  exact hh.symm

lemma candidateBand_extra_sector {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (p : (ℕ × ℕ) → ℕ) (hp : p = Prod.fst ∨ p = Prod.snd) :
    fiberGroup (fun i => p (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val) =
    fiberGroup (fun i => p (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val) ⊓
      sectorGroup (fun i => (candidateExtraSplit r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    have H := hg i
    obtain ⟨j,hj⟩ := (candidateExtraSplit r).symm.surjective i
    obtain ⟨k,hk⟩ := (candidateExtraSplit r).symm.surjective (g i)
    change (candidateExtraSplit r (g i)).isLeft = true ↔ (candidateExtraSplit r i).isLeft = true
    rw [← hk, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change p (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr (g i)))).val =
      p (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val at H
    rw [← hk, ← hj] at H
    cases k with
    | inl k =>
      cases j with
      | inl j => rfl
      | inr j =>
        rw [candidateBandSplit_NE, candidateBandSplit_SW] at H
        have hx := (ShortColumns.mem_shape b δ (s₁ k).val.1 (s₁ k).val.2).mp (s₁ k).property
        have hy := (ShortColumns.mem_shape b δ (s₂ j).val.1 (s₂ j).val.2).mp (s₂ j).property
        rcases hp with rfl | rfl <;> dsimp only [candidateNECell, Prod.swap] at H <;> omega
    | inr k =>
      cases j with
      | inr j => rfl
      | inl j =>
        rw [candidateBandSplit_SW, candidateBandSplit_NE] at H
        have hx := (ShortColumns.mem_shape b δ (s₂ k).val.1 (s₂ k).val.2).mp (s₂ k).property
        have hy := (ShortColumns.mem_shape b δ (s₁ j).val.1 (s₁ j).val.2).mp (s₁ j).property
        rcases hp with rfl | rfl <;> dsimp only [candidateNECell, Prod.swap] at H <;> omega
  · exact inf_le_left

lemma candidateBandRow_NE_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val.1) =
      columnGroup (transposeTableau s₁) := by
  simp_rw [candidateBandSplit_NE]
  rfl

lemma candidateBandRow_SW_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val.1) =
      columnGroup s₂ := by
  simp_rw [candidateBandSplit_SW]
  apply Subgroup.ext
  intro g
  change (∀ i, M-1+(s₂ (g i)).val.2 = M-1+(s₂ i).val.2) ↔ (∀ i, (s₂ (g i)).val.2 = (s₂ i).val.2)
  simp only [Nat.add_left_cancel_iff]

lemma candidateBandCol_NE_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val.2) =
      columnGroup s₁ := by
  simp_rw [candidateBandSplit_NE]
  apply Subgroup.ext
  intro g
  change (∀ i, M-1+(s₁ (g i)).val.2 = M-1+(s₁ i).val.2) ↔ (∀ i, (s₁ (g i)).val.2 = (s₁ i).val.2)
  simp only [Nat.add_left_cancel_iff]

lemma candidateBandCol_SW_group {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val.2) =
      columnGroup (transposeTableau s₂) := by
  simp_rw [candidateBandSplit_SW]
  rfl

end UniversalTensorSquare
end
end

end OAI
