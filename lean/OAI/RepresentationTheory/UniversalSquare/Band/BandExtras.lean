import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandSeparated
import OAI.RepresentationTheory.UniversalSquare.Band.TwoExtras

namespace OAI

/-! Band Extras. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

def bandNELetter {M b δ : ℕ} (hM : 4 ≤ M) :=
  pairLetterMap (bandLongRowLetter (b := b) (δ := δ) hM) (bandShortColLetter (b := b) (δ := δ) hM)

def bandSWLetter {M b δ : ℕ} (hM : 4 ≤ M) :=
  pairLetterMap ((bandShortRowLetter (b := b) (δ := δ) hM) ∘ Fin.cast
    (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose (ShortColumns.shape b δ)))) (bandLongColLetter (b := b) (δ := δ) hM)

lemma bandNELetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandNELetter M b δ hM) :=
  pairLetterMap_injective _ _ (bandExtraLetter_injective _) (Fin.castLE_injective _)

lemma bandSWLetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandSWLetter M b δ hM) :=
  pairLetterMap_injective _ _ ((Fin.castLE_injective _).comp (Fin.cast_injective _))
    (bandExtraLetter_injective _)

lemma candidateExtrasWord_eq {M b δ r : ℕ} (hM : 4 ≤ M)
    (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidateExtrasWord hM s₁ s₂ = positionProduct (candidateExtraSplit r)
      (letterLift (bandNELetter hM) (rowColumnWord s₁))
      (letterLift (bandSWLetter hM) (rowColumnWord (transposeTableau s₂))) := by
  unfold candidateExtrasWord rowColumnWord bandNELetter bandSWLetter
  rw [letterLift_wordTensor, letterLift_wordTensor, ← letterLift_comp]
  rw [polytabloid_doubleTranspose]

lemma bandNELetter_high {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    2 ≤ ((finProdFinEquiv.symm (@bandNELetter M b δ hM x)).1).val := by
  simpa only [bandNELetter, pairLetterMap, Equiv.symm_apply_apply, bandLongRowLetter]
    using bandExtraLetter_high hM _ (finProdFinEquiv.symm x).1

lemma bandSWLetter_low {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    ((finProdFinEquiv.symm (@bandSWLetter M b δ hM x)).1).val < 2 := by
  simp only [bandSWLetter, pairLetterMap, Equiv.symm_apply_apply,
    Function.comp_apply, bandShortRowLetter, Fin.val_castLE, Fin.val_cast]
  have h := (finProdFinEquiv.symm x).1.isLt
  have he := congrArg (fun μ : YoungDiagram => μ.colLen 0)
    (YoungDiagram.transpose_transpose (ShortColumns.shape b δ))
  have hh := ShortColumns.height_le b δ
  omega

theorem candidateExtrasWord_support {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (η : YoungDiagram) (hη : η.card = 2*r) (t : Tableau (2*r) η)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r) _) (candidateExtrasWord hM s₁ s₂)).toRepresentation,
      F ≠ 0 := by
  rw [candidateExtrasWord_eq]
  have hb : r/2 = b := by omega
  have hδ' : r%2 = δ := by omega
  have H := ShortColumns.two_extras r
    ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0)
  rw [hb,hδ'] at H
  exact H s₁ s₂ (bandNELetter hM) (bandSWLetter hM)
    (bandNELetter_injective hM) (bandSWLetter_injective hM)
    (fun a => 2 ≤ (finProdFinEquiv.symm a).1.val)
    (bandNELetter_high hM) (fun a => Nat.not_le.mpr (bandSWLetter_low hM a))
    (candidateExtraSplit r) η hη t he hd

end UniversalTensorSquare
end
end

end OAI
