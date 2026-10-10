import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateShuffle
import OAI.RepresentationTheory.UniversalSquare.Band.BandPositions

namespace OAI

/-! Band Seeds. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateSeparatedRow_extra {M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    2 ≤ (candidateSeparatedRow M b δ hM x).val.2 ↔ x.val ∈ attachmentNE M b δ := by
  rw [candidateSeparatedRow_band M b δ hM hδ x hx]
  have hm := mem_candidate.mp x.property
  rcases x with ⟨⟨i,j⟩,hm0⟩
  simp only [mem_attachmentNE]
  dsimp only at *
  split_ifs <;> omega

def candidateComplementRowShuffle (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidateComplement M b δ) :=
  (candidateRowShuffle M b δ hM).subtypePerm (fun x => by
    have h := candidateRowShuffle_triangle M b δ hM x
    omega)

lemma candidateComplementRowShuffle_val (M b δ : ℕ) (hM : 4 ≤ M)
    (x : candidateComplement M b δ) :
    (candidateComplementRowShuffle M b δ hM x).val =
      candidateRowShuffle M b δ hM x.val := rfl

def candidateBandRowShuffle {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.1) :=
  ⟨((candidateComplementEquiv t).trans (candidateComplementRowShuffle M b δ hM)).trans
      (candidateComplementEquiv t).symm, by
    intro i
    have he := (candidateComplementEquiv t).apply_symm_apply
      (candidateComplementRowShuffle M b δ hM (candidateComplementEquiv t i))
    exact congrArg (fun x : candidateComplement M b δ => x.val.val.1) he⟩

lemma candidateBandRowShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandRowShuffle hM t).val i) =
      candidateRowShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementRowShuffle M b δ hM (candidateComplementEquiv t i)))

def candidateBandRowSeed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :=
  (rightWord (candidateCutPositions t)
    (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t).val)) ∘
      (candidateBandRowShuffle hM t).val

lemma candidateBandRowSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandRowSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateBandTableau t i)).val.2 := by
  rw [candidateBandRowSeed, Function.comp_apply, candidateBandRow_seed,
    candidateBandRowShuffle_cell]
  rfl

lemma candidateBandRowSeed_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    2 ≤ (candidateBandRowSeed hM t i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ := by
  rw [candidateBandRowSeed_val]
  exact candidateSeparatedRow_extra hM hδ _ (candidateBandTableau_outside t i)

theorem candidateBandRow_project_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val ∈ attachmentNE M b δ) (candidateBandRow hM t) =
    signC (candidateBandRowShuffle hM t).val •
      altWord (fiberGroup (fun i => (candidateBandTableau t i).val.1) ⊓
        sectorGroup (fun i => (candidateBandTableau t i).val ∈ attachmentNE M b δ))
          (candidateBandRowSeed hM t) := by
  exact altWord_sector_rotated _ _ (fun a => 2 ≤ a.val) _
    (candidateBandRowShuffle hM t) (candidateBandRowSeed_extra hM hδ t)

def candidateColShuffle (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidate M b δ).cells :=
  ((candidateSwap M b δ).trans (candidateRowShuffle M b δ hM)).trans
    (candidateSwap M b δ)

lemma candidateColShuffle_triangle (M b δ : ℕ) (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) :
    (candidateColShuffle M b δ hM x).val.1 + (candidateColShuffle M b δ hM x).val.2 < M-2 ↔
      x.val.1+x.val.2 < M-2 := by
  have h := candidateRowShuffle_triangle M b δ hM (candidateSwap M b δ x)
  change (candidateRowShuffle M b δ hM (candidateSwap M b δ x)).val.2 +
    (candidateRowShuffle M b δ hM (candidateSwap M b δ x)).val.1 < M-2 ↔ _
  change _ ↔ x.val.2+x.val.1 < M-2 at h
  simpa only [Nat.add_comm] using h

def candidateComplementColShuffle (M b δ : ℕ) (hM : 4 ≤ M) :
    Equiv.Perm (candidateComplement M b δ) :=
  (candidateColShuffle M b δ hM).subtypePerm (fun x => by
    have h := candidateColShuffle_triangle M b δ hM x
    omega)

def candidateBandColShuffle {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    fiberGroup (fun i => (candidateBandTableau t i).val.2) :=
  ⟨((candidateComplementEquiv t).trans (candidateComplementColShuffle M b δ hM)).trans
      (candidateComplementEquiv t).symm, by
    intro i
    have he := (candidateComplementEquiv t).apply_symm_apply
      (candidateComplementColShuffle M b δ hM (candidateComplementEquiv t i))
    exact congrArg (fun x : candidateComplement M b δ => x.val.val.2) he⟩

lemma candidateBandColShuffle_cell {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    candidateBandTableau t ((candidateBandColShuffle hM t).val i) =
      candidateColShuffle M b δ hM (candidateBandTableau t i) := by
  exact congrArg (fun x : candidateComplement M b δ => x.val)
    ((candidateComplementEquiv t).apply_symm_apply
      (candidateComplementColShuffle M b δ hM (candidateComplementEquiv t i)))

def candidateBandColSeed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :=
  (rightWord (candidateCutPositions t)
    (rowWord t ∘ (candidateRotateColPositions hM t).val)) ∘
      (candidateBandColShuffle hM t).val

lemma candidateBandColSeed_val {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (candidateBandColSeed hM t i).val =
      (candidateSeparatedRow M b δ hM (candidateSwap M b δ (candidateBandTableau t i))).val.2 := by
  rw [candidateBandColSeed, Function.comp_apply, candidateBandCol_seed,
    candidateBandColShuffle_cell]
  simp only [candidateRotateCol, candidateColShuffle, candidateSeparatedRow,
    Equiv.trans_apply]
  rfl

lemma candidateBandColSeed_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    2 ≤ (candidateBandColSeed hM t i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ := by
  rw [candidateBandColSeed_val]
  apply candidateSeparatedRow_extra hM hδ
  have h := candidateBandTableau_outside t i
  change M-2 ≤ (candidateBandTableau t i).val.2+(candidateBandTableau t i).val.1
  omega

theorem candidateBandCol_project_extra {n M b δ : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) :
    coordinateProjection (fun w => ∀ i, 2 ≤ (w i).val ↔
      (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ) (candidateBandCol hM t) =
    signC (candidateBandColShuffle hM t).val •
      altWord (fiberGroup (fun i => (candidateBandTableau t i).val.2) ⊓
        sectorGroup (fun i => (candidateBandTableau t i).val.swap ∈ attachmentNE M b δ))
          (candidateBandColSeed hM t) := by
  exact altWord_sector_rotated _ _ (fun a => 2 ≤ a.val) _
    (candidateBandColShuffle hM t) (candidateBandColSeed_extra hM hδ t)

end UniversalTensorSquare
end
end

end OAI
