import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandLetters
import OAI.RepresentationTheory.UniversalSquare.Band.BandGroups

namespace OAI

/-! Band Factor. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

def candidatePathRow {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :=
  altWord (fiberGroup (fun i => (candidateBandTableau t
    ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val.1))
      (leftWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t))

def candidatePathCol {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :=
  altWord (fiberGroup (fun i => (candidateBandTableau t
    ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val.2))
      (leftWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t))

def bandLongRowLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin ((ShortColumns.shape b δ).transpose.colLen 0) → Fin ((candidate M b δ).transpose.colLen 0) :=
  bandExtraLetter (le_of_eq (candidateRowAlphabet_size hM).symm)

def bandShortRowLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin ((ShortColumns.shape b δ).colLen 0) → Fin ((candidate M b δ).transpose.colLen 0) :=
  Fin.castLE ((ShortColumns.height_le b δ).trans (by rw [candidateRowAlphabet_size hM]; omega))

def bandLongColLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin ((ShortColumns.shape b δ).transpose.colLen 0) → Fin ((candidate M b δ).colLen 0) :=
  bandExtraLetter (le_of_eq (candidateColAlphabet_size hM).symm)

def bandShortColLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin ((ShortColumns.shape b δ).colLen 0) → Fin ((candidate M b δ).colLen 0) :=
  Fin.castLE ((ShortColumns.height_le b δ).trans (by rw [candidateColAlphabet_size hM]; omega))

lemma candidateBandRow_extras {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    altWord (fiberGroup (fun i => (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val.1))
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      positionProduct (candidateExtraSplit r)
        (letterLift (bandLongRowLetter hM) (polytabloid (transposeTableau s₁)))
        (letterLift (bandShortRowLetter hM) (polytabloid s₂)) := by
  rw [candidateBand_extra_sector hM t s₁ s₂ Prod.fst (Or.inl rfl), altWord_fiber_split,
    candidateBandRow_NE_group, candidateBandRow_SW_group,
    candidateBandRowSeed_NE hM hδ, candidateBandRowSeed_SW hM hδ]
  simp only [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma candidateBandCol_extras {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    altWord (fiberGroup (fun i => (candidateBandTableau t
      ((candidateBandSplit hM t s₁ s₂).symm (Sum.inr i))).val.2))
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      positionProduct (candidateExtraSplit r)
        (letterLift (bandShortColLetter hM) (polytabloid s₁))
        (letterLift (bandLongColLetter hM) (polytabloid (transposeTableau s₂))) := by
  rw [candidateBand_extra_sector hM t s₁ s₂ Prod.snd (Or.inr rfl), altWord_fiber_split,
    candidateBandCol_NE_group, candidateBandCol_SW_group,
    candidateBandColSeed_NE hM hδ, candidateBandColSeed_SW hM hδ]
  simp only [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma candidateBandRow_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ) (candidateBandRow hM t) =
    signC (candidateBandRowShuffle hM t).val •
      positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathRow hM t s₁ s₂)
        (positionProduct (candidateExtraSplit r)
          (letterLift (bandLongRowLetter hM) (polytabloid (transposeTableau s₁)))
          (letterLift (bandShortRowLetter hM) (polytabloid s₂))) := by
  rw [candidateBandRow_project_extra hM hδ, candidateBandRow_sector_eq hM t s₁ s₂,
    altWord_fiber_split, candidateBandRow_extras hM hδ]
  rfl

lemma candidateBandCol_factor {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) (candidateBandCol hM t) =
    signC (candidateBandColShuffle hM t).val •
      positionProduct (candidateBandSplit hM t s₁ s₂) (candidatePathCol hM t s₁ s₂)
        (positionProduct (candidateExtraSplit r)
          (letterLift (bandShortColLetter hM) (polytabloid s₁))
          (letterLift (bandLongColLetter hM) (polytabloid (transposeTableau s₂)))) := by
  rw [candidateBandCol_project_extra hM hδ, candidateBandCol_sector_eq hM t s₁ s₂,
    altWord_fiber_split, candidateBandCol_extras hM hδ]
  rfl

end UniversalTensorSquare
end
end

end OAI
