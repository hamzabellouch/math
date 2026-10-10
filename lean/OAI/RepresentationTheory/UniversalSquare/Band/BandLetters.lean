import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandSeeds
import OAI.RepresentationTheory.UniversalSquare.Band.BandSplit

namespace OAI

/-! Band Letters. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateSeparatedRow_NE {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (z : (ShortColumns.shape b δ).cells)
    (hx : x.val = candidateNECell M z) :
    (candidateSeparatedRow M b δ hM x).val.2 =
      if z.val.2 < b then M-1+z.val.2 else M+z.val.2 := by
  classical
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [candidateSeparatedRow_band M b δ hM hδ x (by rw [hx]; dsimp [candidateNECell]; omega), hx]
  dsimp +instances only [candidateNECell]
  split_ifs <;> omega

lemma candidateSeparatedRow_SW {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (z : (ShortColumns.shape b δ).cells)
    (hx : x.val = (candidateNECell M z).swap) :
    (candidateSeparatedRow M b δ hM x).val.2 = z.val.1 := by
  classical
  have hz := (ShortColumns.mem_shape b δ z.val.1 z.val.2).mp z.property
  rw [candidateSeparatedRow_band M b δ hM hδ x (by rw [hx]; dsimp [candidateNECell]; omega), hx]
  dsimp +instances only [candidateNECell, Prod.swap]
  split_ifs <;> omega

lemma shortColumns_width (b δ : ℕ) : (ShortColumns.shape b δ).transpose.colLen 0 = b+δ := by
  rw [YoungDiagram.colLen_transpose]
  have H (j : ℕ) : j < (ShortColumns.shape b δ).rowLen 0 ↔ j < b+δ := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, ShortColumns.mem_shape]
    simp only [true_and, zero_ne_one, false_and, or_false]
  have h₁ := H (b+δ)
  have h₂ := H ((ShortColumns.shape b δ).rowLen 0)
  omega

def bandSmallLetter {D : ℕ} (hD : 2 ≤ D) : Fin 2 → Fin D := Fin.castLE hD

lemma bandSmallLetter_injective {D : ℕ} (hD : 2 ≤ D) :
    Function.Injective (bandSmallLetter hD) := Fin.castLE_injective hD

def bandExtraLetter {M b δ D : ℕ} (hD : M+b+δ ≤ D) :
    Fin ((ShortColumns.shape b δ).transpose.colLen 0) → Fin D :=
  fun c => ⟨if c.val < b then M-1+c.val else M+c.val, by
    have hc := c.isLt
    have hc' : c.val < b+δ := by simpa only [shortColumns_width] using hc
    split_ifs <;> omega⟩

lemma bandExtraLetter_injective {M b δ D : ℕ} (hD : M+b+δ ≤ D) :
    Function.Injective (@bandExtraLetter M b δ D hD) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [bandExtraLetter] at hv
  split_ifs at hv <;> omega

lemma bandExtraLetter_high {M b δ D : ℕ} (hM : 4 ≤ M) (hD : M+b+δ ≤ D)
    (c : Fin ((ShortColumns.shape b δ).transpose.colLen 0)) :
    2 ≤ (bandExtraLetter hD c).val := by
  dsimp only [bandExtraLetter]
  split_ifs <;> omega

lemma candidateRowAlphabet_size {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).transpose.colLen 0 = M+b+δ := by
  rw [candidate_transpose, candidate_colLen M b δ 0 hM]
  rfl

lemma candidateColAlphabet_size {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).colLen 0 = M+b+δ := by
  rw [candidate_colLen M b δ 0 hM]
  rfl

lemma candidateBandRowSeed_NE {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    leftWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      bandExtraLetter (le_of_eq (candidateRowAlphabet_size hM).symm) ∘
        rowWord (transposeTableau s₁) := by
  funext i
  apply Fin.ext
  rw [leftWord, rightWord, candidateBandRowSeed_val]
  exact candidateSeparatedRow_NE hM hδ _ (s₁ i) (candidateBandSplit_NE hM t s₁ s₂ i)

lemma candidateBandRowSeed_SW {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    rightWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandRowSeed hM t)) =
      Fin.castLE (show (ShortColumns.shape b δ).colLen 0 ≤
        (candidate M b δ).transpose.colLen 0 from
        (ShortColumns.height_le b δ).trans (by rw [candidateRowAlphabet_size hM]; omega)) ∘
          rowWord s₂ := by
  funext i
  apply Fin.ext
  rw [rightWord, rightWord, candidateBandRowSeed_val]
  exact candidateSeparatedRow_SW hM hδ _ (s₂ i) (candidateBandSplit_SW hM t s₁ s₂ i)

lemma candidateBandColSeed_NE {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    leftWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      Fin.castLE (show (ShortColumns.shape b δ).colLen 0 ≤
        (candidate M b δ).colLen 0 from
        (ShortColumns.height_le b δ).trans (by rw [candidateColAlphabet_size hM]; omega)) ∘
          rowWord s₁ := by
  funext i
  apply Fin.ext
  rw [leftWord, rightWord, candidateBandColSeed_val]
  apply candidateSeparatedRow_SW hM hδ _ (s₁ i)
  change (candidateBandTableau t _).val.swap = _
  rw [candidateBandSplit_NE]

lemma candidateBandColSeed_SW {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    rightWord (candidateExtraSplit r)
      (rightWord (candidateBandSplit hM t s₁ s₂) (candidateBandColSeed hM t)) =
      bandExtraLetter (le_of_eq (candidateColAlphabet_size hM).symm) ∘
        rowWord (transposeTableau s₂) := by
  funext i
  apply Fin.ext
  rw [rightWord, rightWord, candidateBandColSeed_val]
  apply candidateSeparatedRow_NE hM hδ _ (s₂ i)
  change (candidateBandTableau t _).val.swap = _
  rw [candidateBandSplit_SW, Prod.swap_swap]

end UniversalTensorSquare
end
end

end OAI
