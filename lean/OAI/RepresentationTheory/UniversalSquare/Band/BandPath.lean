import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking
import OAI.RepresentationTheory.UniversalSquare.Band.BandSeparated

namespace OAI

/-! Band Path. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl
open scoped TensorProduct

def candidatePathEquiv {M : ℕ} (hM : 4 ≤ M) : Fin (2*(M-1)+1) ≃ Fin (2*M-1) :=
  finCongr (by omega)

def bandSmallRowLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin 2 → Fin ((candidate M b δ).transpose.colLen 0) :=
  bandSmallLetter (by rw [candidateRowAlphabet_size hM]; omega)

def bandSmallColLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin 2 → Fin ((candidate M b δ).colLen 0) :=
  bandSmallLetter (by rw [candidateColAlphabet_size hM]; omega)

lemma candidatePathRow_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathRow hM t s₁ s₂ =
      letterLift (bandSmallRowLetter hM)
        (relabelWord (candidatePathEquiv hM) (PathLayer.rowAlt (M-1))) := by
  unfold PathLayer.rowAlt
  rw [altWord_relabel, letterLift_altWord]
  unfold candidatePathRow
  congr 1
  · apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ (∀ i, _ = _)
    apply forall_congr'
    intro i
    simp only [candidateBandSplit_path]
    exact candidatePathCell_row_tag hM _ _
  · funext i
    apply Fin.ext
    rw [Function.comp_apply]
    change (candidateBandRowSeed hM t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val = _
    rw [candidateBandRowSeed_val, candidateSeparatedRow_path hM hδ _ i
      (candidateBandSplit_path hM t s₁ s₂ i)]
    simp only [bandSmallRowLetter, bandSmallLetter, Fin.val_castLE, Function.comp_apply,
      PathLayer.base, candidatePathEquiv, finCongr_symm, finCongr_apply, Fin.val_cast]
    split_ifs <;> rfl

lemma candidatePathCol_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathCol hM t s₁ s₂ =
      letterLift (bandSmallColLetter hM)
        (relabelWord ((Fin.revPerm).trans (candidatePathEquiv hM)) (PathLayer.rowAlt (M-1))) := by
  unfold PathLayer.rowAlt
  rw [altWord_relabel, letterLift_altWord]
  unfold candidatePathCol
  congr 1
  · apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ (∀ i, _ = _)
    apply forall_congr'
    intro i
    simp only [candidateBandSplit_path]
    have hh := candidatePathCell_row_tag (b := b) (δ := δ) hM (g i).rev i.rev
    rw [← candidatePathCell_swap hM, ← candidatePathCell_swap hM] at hh
    simpa only [Prod.fst_swap, Function.comp_apply, PathLayer.tag, Equiv.symm_trans,
      Equiv.trans_apply, candidatePathEquiv, finCongr_symm, finCongr_apply,
      Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, Fin.val_cast,
      show 2*(M-1)+1 = 2*M-1 from by omega] using hh
  · funext i
    apply Fin.ext
    rw [Function.comp_apply]
    change (candidateBandColSeed hM t ((candidateBandSplit hM t s₁ s₂).symm (Sum.inl i))).val = _
    rw [candidateBandColSeed_val, candidateSeparatedRow_path hM hδ _ i.rev (by
      change (candidateBandTableau t _).val.swap = _
      rw [candidateBandSplit_path, candidatePathCell_swap hM])]
    simp only [bandSmallColLetter, bandSmallLetter, Fin.val_castLE, Function.comp_apply,
      PathLayer.base, candidatePathEquiv, Equiv.symm_trans, Equiv.trans_apply,
      finCongr_symm, finCongr_apply, Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_cast, Fin.val_rev,
      show 2*(M-1)+1 = 2*M-1 from by omega]
    split_ifs <;> rfl

def bandPairSmallLetter {M b δ : ℕ} (hM : 4 ≤ M) :
    Fin 4 → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) :=
  pairLetterMap (bandSmallRowLetter hM) (bandSmallColLetter hM)

lemma bandPairSmallLetter_injective {M b δ : ℕ} (hM : 4 ≤ M) :
    Function.Injective (@bandPairSmallLetter M b δ hM) :=
  pairLetterMap_injective _ _ (bandSmallLetter_injective _) (bandSmallLetter_injective _)

theorem candidatePathWord_eq {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidatePathWord hM t s₁ s₂ =
      (-1 : ℂ)^(M-1) • letterLift (bandPairSmallLetter hM)
        (relabelWord (candidatePathEquiv hM) (Path.bandWord (M-1))) := by
  rw [candidatePathWord, candidatePathRow_eq hM hδ, candidatePathCol_eq hM hδ,
    ← letterLift_wordTensor, ← map_smul, ← map_smul]
  congr 1
  ext w
  simp only [wordTensor_tmul, relabelWord_apply, Pi.smul_apply, smul_eq_mul]
  have hr : (splitRight w) ∘ (Fin.revPerm.trans (candidatePathEquiv hM)) =
      (fun i => (Path.parts ((w ∘ candidatePathEquiv hM) i)).2) ∘ Fin.rev := rfl
  rw [hr]
  exact PathLayer.paired_rowAlt (M-1) (w ∘ candidatePathEquiv hM)

theorem candidatePathWord_support {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (μ : YoungDiagram) (u : Tableau (2*M-1) μ) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep u)
      (cyclic (wordRep (2*M-1) _)
        (candidatePathWord hM t s₁ s₂)).toRepresentation, F ≠ 0 := by
  rw [candidatePathWord_eq hM hδ, cyclic_smul_eq _ _ _ (pow_ne_zero _ (by norm_num))]
  obtain ⟨f,hf⟩ := support_relabel (candidatePathEquiv hM) (Path.bandWord (M-1))
    (fun μ u hd => Path.odd_path_support (M-1) μ u hd) μ u hd
  let v := relabelWord (candidatePathEquiv hM) (Path.bandWord (M-1))
  let G := cyclicMap (letterLift (bandPairSmallLetter (b := b) (δ := δ) hM)) v
  refine ⟨G.comp f, ?_⟩
  intro h0
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hz : G (f x) = 0 := congrArg (fun H => H x) h0
  have hGi : Function.Injective G := by
    intro a c he
    apply Subtype.ext
    exact letterLift_injective _ (bandPairSmallLetter_injective hM)
      (congrArg Subtype.val he)
  exact hGi (hz.trans (map_zero G).symm)

end UniversalTensorSquare
end
end

end OAI
