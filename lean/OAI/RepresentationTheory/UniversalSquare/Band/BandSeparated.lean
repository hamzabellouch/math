import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandFactor

namespace OAI

/-! Band Separated. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

def candidateBandPattern {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0)) : Prop :=
  (∀ i, 2 ≤ (splitLeft w i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ) ∧
  (∀ i, 2 ≤ (splitRight w i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ)

def candidatePathWord {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :=
  wordTensor _ _ _ (candidatePathRow hM t s₁ s₂ ⊗ₜ[ℂ] candidatePathCol hM t s₁ s₂)

def candidateExtrasWord {M b δ r : ℕ} (hM : 4 ≤ M)
    (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :=
  positionProduct (candidateExtraSplit r)
    (wordTensor _ _ _
      (letterLift (bandLongRowLetter hM) (polytabloid (transposeTableau s₁)) ⊗ₜ[ℂ]
        letterLift (bandShortColLetter hM) (polytabloid s₁)))
    (wordTensor _ _ _
      (letterLift (bandShortRowLetter hM) (polytabloid s₂) ⊗ₜ[ℂ]
        letterLift (bandLongColLetter hM) (polytabloid (transposeTableau s₂))))

theorem candidateBandPattern_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (candidateBandPattern t) (candidateBandWord hM t) =
      (signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val) •
        positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathWord hM t s₁ s₂)
          (candidateExtrasWord hM s₁ s₂) := by
  change coordinateProjection (fun w =>
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ)
      (splitLeft w) ∧
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ)
      (splitRight w)) _ = _
  rw [candidateBandWord, coordinateProjection_wordTensor
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ)
    (fun v => ∀ i, 2 ≤ (v i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ),
    candidateBandRow_factor hM hδ t s₁ s₂, candidateBandCol_factor hM hδ t s₁ s₂,
    TensorProduct.smul_tmul_smul, map_smul, wordTensor_positionProduct,
    wordTensor_positionProduct]
  rfl

lemma candidateNECell_swap_not_mem {M b δ : ℕ} (hM : 4 ≤ M)
    (z : (ShortColumns.shape b δ).cells) :
    (candidateNECell M z).swap ∉ attachmentNE M b δ := by
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [mem_attachmentNE]
  dsimp only [candidateNECell, Prod.swap]
  omega

lemma candidateBandWord_sector_iff {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) :
    wordSector (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true)
      (candidatePathAlphabet M b δ) w ↔ candidateBandPattern t w := by
  have hw' := hw
  rw [candidateBandWord, wordTensor_tmul] at hw'
  have hr := (mul_ne_zero_iff.mp hw').1
  have hc := (mul_ne_zero_iff.mp hw').2
  have H (i : Fin (candidateBandSize t)) :
      (candidatePathAlphabet M b δ (w i) ↔
        ((candidateBandSplit hM t s₁ s₂) i).isLeft = true) ↔
      ((2 ≤ (splitLeft w i).val ↔ (candidateBandTableau t i).val ∈ attachmentNE M b δ) ∧
       (2 ≤ (splitRight w i).val ↔ (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ)) := by
    obtain ⟨p,rfl⟩ := (candidateBandSplit hM t s₁ s₂).symm.surjective i
    cases p with
    | inl q =>
      rw [candidateBandSplit_path]
      simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,
        (pathCell_not_attachment M b δ hM q).1,
        (pathCell_not_attachment M b δ hM q).2, iff_false,
        not_le, candidatePathAlphabet, splitLeft, splitRight]
    | inr j =>
      obtain ⟨p,rfl⟩ := (candidateExtraSplit r).symm.surjective j
      cases p with
      | inl z =>
        have hc' := candidateBandCol_clearance hM t _ hc
          ((candidateBandSplit hM t s₁ s₂).symm
            (Sum.inr ((candidateExtraSplit r).symm (Sum.inl z)))) (by
          rw [candidateBandSplit_NE]
          dsimp only [candidateNECell]
          omega)
        rw [candidateBandSplit_NE]
        simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,
          candidateNECell_mem hM, candidateNECell_swap_not_mem hM, iff_true]
        change (¬ ((splitLeft w _).val < 2 ∧ (splitRight w _).val < 2)) ↔
          (2 ≤ (splitLeft w _).val ∧ ¬2 ≤ (splitRight w _).val)
        omega
      | inr z =>
        have hr' := candidateBandRow_clearance hM t _ hr
          ((candidateBandSplit hM t s₁ s₂).symm
            (Sum.inr ((candidateExtraSplit r).symm (Sum.inr z)))) (by
          rw [candidateBandSplit_SW]
          dsimp only [candidateNECell, Prod.swap]
          omega)
        rw [candidateBandSplit_SW]
        simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,
          Prod.swap_swap, candidateNECell_mem hM, candidateNECell_swap_not_mem hM, iff_true]
        change (¬ ((splitLeft w _).val < 2 ∧ (splitRight w _).val < 2)) ↔
          (¬2 ≤ (splitLeft w _).val ∧ 2 ≤ (splitRight w _).val)
        omega
  change (∀ i, _) ↔ ((∀ i, _) ∧ ∀ i, _)
  exact (forall_congr' H).trans forall_and

theorem candidateBandWord_separated {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection
        (wordSector (fun i => ((candidateBandSplit hM t s₁ s₂) i).isLeft = true)
          (candidatePathAlphabet M b δ)) (candidateBandWord hM t) =
      (signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val) •
        positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathWord hM t s₁ s₂)
          (candidateExtrasWord hM s₁ s₂) := by
  classical
  rw [← candidateBandPattern_factor hM hδ t s₁ s₂]
  ext w
  simp only [coordinateProjection_apply]
  by_cases hw : candidateBandWord hM t w = 0
  · simp only [hw, ite_self]
  · rw [candidateBandWord_sector_iff hM t s₁ s₂ w hw]

end UniversalTensorSquare
end
end

end OAI
