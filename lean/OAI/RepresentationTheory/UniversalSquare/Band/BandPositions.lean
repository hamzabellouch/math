import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateClearance

namespace OAI

/-! Band Positions. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma candidateBandTableau_injective {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    Function.Injective (candidateBandTableau t) := by
  intro i j h
  have h₁ := t.injective h
  exact Sum.inr_injective ((candidateCutPositions t).symm.injective h₁)

lemma candidateBandTableau_surjective {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (x : (candidate M b δ).cells) (hx : M-2 ≤ x.val.1+x.val.2) :
    ∃ i, candidateBandTableau t i = x := by
  cases he : candidateCutPositions t (t.symm x) with
  | inl i =>
    have ht := (candidateCutPositions_high t (t.symm x)).mp (by rw [he]; rfl)
    change (t (t.symm x)).val.1 + (t (t.symm x)).val.2 < M-2 at ht
    rw [Equiv.apply_symm_apply] at ht
    omega
  | inr i =>
    refine ⟨i, ?_⟩
    change t ((candidateCutPositions t).symm (Sum.inr i)) = x
    rw [← he, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

abbrev candidateComplement (M b δ : ℕ) :=
  {x : (candidate M b δ).cells // M-2 ≤ x.val.1+x.val.2}

def candidateComplementEquiv {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    Fin (candidateBandSize t) ≃ candidateComplement M b δ :=
  Equiv.ofBijective (fun i => ⟨candidateBandTableau t i, candidateBandTableau_outside t i⟩)
    ⟨fun _ _ h => candidateBandTableau_injective t (congrArg Subtype.val h), by
      intro x
      obtain ⟨i,hi⟩ := candidateBandTableau_surjective t x.val x.property
      exact ⟨i, Subtype.ext hi⟩⟩

def candidateNECell (M : ℕ) {b δ : ℕ} (x : (ShortColumns.shape b δ).cells) : ℕ × ℕ :=
  (x.val.1,M-1+x.val.2)

lemma candidateNECell_mem {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (ShortColumns.shape b δ).cells) : candidateNECell M x ∈ attachmentNE M b δ := by
  have hx := (ShortColumns.mem_shape b δ x.val.1 x.val.2).mp x.property
  change (x.val.1,M-1+x.val.2) ∈ attachmentNE M b δ
  rw [mem_attachmentNE]
  omega

lemma candidateNECell_injective (M b δ : ℕ) :
    Function.Injective (candidateNECell M (b := b) (δ := δ)) := by
  intro x y h
  apply Subtype.ext
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext
  · exact h₁
  change M-1+x.val.2 = M-1+y.val.2 at h₂
  omega

lemma candidateNECell_surjective {M b δ : ℕ} (hM : 4 ≤ M) (i j : ℕ)
    (hx : (i,j) ∈ attachmentNE M b δ) :
    ∃ x : (ShortColumns.shape b δ).cells, candidateNECell M x = (i,j) := by
  rw [mem_attachmentNE] at hx
  have hs : (i,j-(M-1)) ∈ ShortColumns.shape b δ := by
    rw [ShortColumns.mem_shape]
    omega
  refine ⟨⟨(i,j-(M-1)),hs⟩, ?_⟩
  apply Prod.ext
  · rfl
  change M-1 + (j-(M-1)) = j
  omega

abbrev CandidateBandParts (M b δ : ℕ) :=
  Fin (2*M-1) ⊕ (ShortColumns.shape b δ).cells ⊕ (ShortColumns.shape b δ).cells

def candidatePartsCell (M b δ : ℕ) (hM : 4 ≤ M) :
    CandidateBandParts M b δ → candidateComplement M b δ
  | .inl q => ⟨⟨candidatePathCell M b δ q, (candidatePathCell_mem M b δ hM q).1⟩,
      (candidatePathCell_mem M b δ hM q).2⟩
  | .inr (.inl x) => ⟨⟨candidateNECell M x,
      (attachmentNE_mem M b δ hM (candidateNECell_mem hM x)).1⟩,
      (attachmentNE_mem M b δ hM (candidateNECell_mem hM x)).2⟩
  | .inr (.inr x) => ⟨⟨(candidateNECell M x).swap, by
      have hx := (attachmentNE_mem M b δ hM (candidateNECell_mem hM x)).1
      have ht : (candidateNECell M x).swap ∈ (candidate M b δ).transpose := by
        simpa only [YoungDiagram.mem_transpose, Prod.swap_swap, candidateNECell] using hx
      simpa only [candidate_transpose, YoungDiagram.mem_cells] using ht⟩, by
        have hx := (attachmentNE_mem M b δ hM (candidateNECell_mem hM x)).2
        change M-2 ≤ (candidateNECell M x).2 + (candidateNECell M x).1
        dsimp only [candidateNECell] at *
        omega⟩

lemma candidatePartsCell_injective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidatePartsCell M b δ hM) := by
  intro x y he
  have h := congrArg (fun z : candidateComplement M b δ => z.val.val) he
  rcases x with i | (x | x) <;> rcases y with j | (y | y) <;>
    dsimp only [candidatePartsCell] at h
  · exact congrArg Sum.inl (candidatePathCell_injective M b δ hM h)
  · exact False.elim ((pathCell_not_attachment M b δ hM i).1
      (h.symm ▸ candidateNECell_mem hM y))
  · have hh := congrArg Prod.swap h
    rw [Prod.swap_swap] at hh
    exact False.elim ((pathCell_not_attachment M b δ hM i).2
      (hh.symm ▸ candidateNECell_mem hM y))
  · exact False.elim ((pathCell_not_attachment M b δ hM j).1
      (h ▸ candidateNECell_mem hM x))
  · exact congrArg (Sum.inr ∘ Sum.inl) (candidateNECell_injective M b δ h)
  · have hx := candidateNECell_mem hM x
    have hy := candidateNECell_mem hM y
    have hd := attachment_disjoint_transpose M b δ hM
    exact False.elim (Finset.disjoint_left.mp hd hx
      (h.symm ▸ Finset.mem_map.mpr ⟨candidateNECell M y,hy,rfl⟩))
  · have hh := congrArg Prod.swap h
    rw [Prod.swap_swap] at hh
    exact False.elim ((pathCell_not_attachment M b δ hM j).2
      (hh ▸ candidateNECell_mem hM x))
  · have hx := candidateNECell_mem hM x
    have hy := candidateNECell_mem hM y
    have hd := attachment_disjoint_transpose M b δ hM
    exact False.elim (Finset.disjoint_left.mp hd hy
      (h ▸ Finset.mem_map.mpr ⟨candidateNECell M x,hx,rfl⟩))
  · have hh := congrArg Prod.swap h
    simp only [Prod.swap_swap] at hh
    exact congrArg (Sum.inr ∘ Sum.inr) (candidateNECell_injective M b δ hh)

lemma candidatePartsCell_surjective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Surjective (candidatePartsCell M b δ hM) := by
  intro x
  obtain ⟨⟨⟨i,j⟩,hx⟩,ht⟩ := x
  rcases candidate_band_cell_decomposition M b δ hM i j hx ht with ⟨q,hq⟩ | hn | hs
  · exact ⟨Sum.inl q, Subtype.ext (Subtype.ext hq)⟩
  · obtain ⟨y,hy⟩ := candidateNECell_surjective hM i j hn
    exact ⟨Sum.inr (Sum.inl y), Subtype.ext (Subtype.ext hy)⟩
  · obtain ⟨y,hy⟩ := candidateNECell_surjective hM j i hs
    exact ⟨Sum.inr (Sum.inr y), Subtype.ext (Subtype.ext (congrArg Prod.swap hy))⟩

def candidateBandPartsEquiv {n M b δ r : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    Fin (candidateBandSize t) ≃ Fin (2*M-1) ⊕ (Fin r ⊕ Fin r) :=
  ((candidateComplementEquiv t).trans
    (Equiv.ofBijective (candidatePartsCell M b δ hM)
      ⟨candidatePartsCell_injective M b δ hM,candidatePartsCell_surjective M b δ hM⟩).symm).trans
        (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr s₁.symm s₂.symm))

end UniversalTensorSquare
end
end

end OAI
