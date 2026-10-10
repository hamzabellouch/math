import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateShuffle
import OAI.RepresentationTheory.UniversalSquare.Band.BandPositions

namespace OAI

/-! Band Split. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateBandParts_cell {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (x : Fin (2*M-1) ⊕ (Fin r ⊕ Fin r)) :
    (candidateBandTableau t ((candidateBandPartsEquiv hM t s₁ s₂).symm x)).val =
      (candidatePartsCell M b δ hM
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr s₁ s₂)) x)).val.val := by
  change ((candidateComplementEquiv t)
    (((candidateComplementEquiv t).symm)
      (candidatePartsCell M b δ hM _))).val.val = _
  rw [Equiv.apply_symm_apply]
  rfl

def candidateBandSplit {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    Fin (candidateBandSize t) ≃ Fin (2*M-1) ⊕ Fin (2*r) :=
  (candidateBandPartsEquiv hM t s₁ s₂).trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.trans (finCongr (by omega))))

def candidateExtraSplit (r : ℕ) : Fin (2*r) ≃ Fin r ⊕ Fin r :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

lemma candidateBandSplit_path {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (q : Fin (2*M-1)) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl q))).val =
      candidatePathCell M b δ q :=
  candidateBandParts_cell hM t s₁ s₂ (Sum.inl q)

lemma candidateBandSplit_NE {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (i : Fin r) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inl i))))).val =
        candidateNECell M (s₁ i) := by
  simpa only [candidateBandSplit, candidateExtraSplit, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, candidatePartsCell,
    Sum.map_inl, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
    using candidateBandParts_cell hM t s₁ s₂ (Sum.inr (Sum.inl i))

lemma candidateBandSplit_SW {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (i : Fin r) :
    (candidateBandTableau t ((candidateBandSplit hM t s₁ s₂).symm
      (Sum.inr ((candidateExtraSplit r).symm (Sum.inr i))))).val =
        (candidateNECell M (s₂ i)).swap := by
  simpa only [candidateBandSplit, candidateExtraSplit, Equiv.symm_trans, Equiv.trans_apply,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, candidatePartsCell,
    Sum.map_inl, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
    using candidateBandParts_cell hM t s₁ s₂ (Sum.inr (Sum.inr i))

lemma candidatePathCell_row_tag {M b δ : ℕ} (hM : 4 ≤ M)
    (i j : Fin (2*M-1)) :
    (candidatePathCell M b δ i).1 = (candidatePathCell M b δ j).1 ↔
      (i.val+1)/2 = (j.val+1)/2 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold candidatePathCell
  split_ifs <;> dsimp only <;> omega

lemma candidatePathCell_swap {M b δ : ℕ} (hM : 4 ≤ M)
    (i : Fin (2*M-1)) :
    (candidatePathCell M b δ i).swap = candidatePathCell M b δ i.rev := by
  have hi := i.isLt
  unfold candidatePathCell
  simp only [Fin.val_rev]
  split_ifs <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] <;> omega

lemma candidateSeparatedRow_path {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (q : Fin (2*M-1))
    (hx : x.val = candidatePathCell M b δ q) :
    (candidateSeparatedRow M b δ hM x).val.2 = if q.val = 0 then 0 else (q.val+1)%2 := by
  have hq := q.isLt
  rw [candidateSeparatedRow_band M b δ hM hδ x (by
    rw [hx]; exact (candidatePathCell_mem M b δ hM q).2), hx]
  unfold candidatePathCell
  split_ifs <;> dsimp only at * <;> omega

lemma candidateParts_row_sectors {M b δ : ℕ} (hM : 4 ≤ M)
    (x y : CandidateBandParts M b δ)
    (hrow : (candidatePartsCell M b δ hM x).val.val.1 =
      (candidatePartsCell M b δ hM y).val.val.1) :
    (Sum.isLeft x = true ↔ Sum.isLeft y = true) ↔
      ((candidatePartsCell M b δ hM x).val.val ∈ attachmentNE M b δ ↔
        (candidatePartsCell M b δ hM y).val.val ∈ attachmentNE M b δ) := by
  have H (q : Fin (2*M-1)) (z : (ShortColumns.shape b δ).cells) :
      (candidatePathCell M b δ q).1 ≠ (candidateNECell M z).2 := by
    have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
    have hq := q.isLt
    unfold candidatePathCell candidateNECell
    split_ifs <;> dsimp only <;> omega
  have N (z : (ShortColumns.shape b δ).cells) :
      (candidateNECell M z).swap ∉ attachmentNE M b δ := by
    have hz := candidateNECell_mem hM z
    simp only [mem_attachmentNE, candidateNECell, Prod.swap_prod_mk] at hz ⊢
    omega
  rcases x with x | (x | x) <;> rcases y with y | (y | y) <;>
    dsimp only [candidatePartsCell] at hrow ⊢
  all_goals try simp only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true,
    true_iff, false_iff, (pathCell_not_attachment M b δ hM _).1,
    candidateNECell_mem hM, N, iff_self]
  all_goals try first | exact False.elim (H _ _ hrow) |
    exact False.elim (H _ _ hrow.symm) | trivial
  all_goals have hx := (ShortColumns.mem_shape b δ x.val.1 x.val.2).mp x.property
  all_goals have hy := (ShortColumns.mem_shape b δ y.val.1 y.val.2).mp y.property
  all_goals dsimp only [candidateNECell, Prod.swap] at hrow
  all_goals omega

lemma candidateBandRow_sector_eq {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
      sectorGroup (fun i => (candidateBandTableau t i).val ∈ attachmentNE M b δ) =
    fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
      sectorGroup (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) := by
  apply Subgroup.ext
  intro g
  change ((∀ i, (candidateBandTableau t (g i)).val.1 = (candidateBandTableau t i).val.1) ∧ _) ↔
    ((∀ i, (candidateBandTableau t (g i)).val.1 = (candidateBandTableau t i).val.1) ∧ _)
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
  have hh := candidateParts_row_sectors hM (f (E (g i))) (f (E i)) (by
    rw [← H, ← H]; exact hg i)
  dsimp only at *
  simp_rw [H]
  have hside (j) : (f (E j)).isLeft = ((candidateBandSplit hM t s₁ s₂) j).isLeft := by
    dsimp only [candidateBandSplit, Equiv.trans_apply, f]
    cases E j <;> rfl
  rw [hside, hside] at hh
  exact hh.symm

end UniversalTensorSquare
end
end

end OAI
