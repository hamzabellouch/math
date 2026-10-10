import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.PairSwap
import OAI.RepresentationTheory.UniversalSquare.Specht.ShortColumns

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

def columnSquareWord {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    WordSpace n (α.colLen 0 * α.colLen 0) :=
  wordTensor _ _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)

def columnSquareCyclic {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :=
  cyclic (wordRep n (α.colLen 0 * α.colLen 0)) (columnSquareWord t)

def rowColumnTransposeCyclicMap {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    Representation.IntertwiningMap (rowColumnCyclic (transposeTableau t)).toRepresentation
      (rowColumnCyclic t).toRepresentation where
  toLinearMap := ((rowColumnTransposeMap t).toLinearMap.comp
    (rowColumnCyclic (transposeTableau t)).toSubmodule.subtype).codRestrict _ (by
      intro x
      have h := intertwiner_cyclic_mem (rowColumnTransposeMap t)
        (rowColumnWord (transposeTableau t)) x.val x.property
      rw [rowColumnTransposeMap_word t] at h
      exact h)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun ((rowColumnTransposeMap t).isIntertwining' g) x.val

lemma rowColumnTransposeCyclicMap_injective {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    Function.Injective (rowColumnTransposeCyclicMap t) := by
  intro x y h
  apply Subtype.ext
  exact rowColumnTransposeMap_injective t (congrArg Subtype.val h)

theorem sign_rowColumn_support_of_columnSquare {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (columnSquareCyclic t).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  let T := transposeTableau (transposeTableau t)
  let F := pairWordMap (n := n) (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
    (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
  have hF : F (columnSquareWord T) = columnSquareWord t := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, polytabloid_doubleTranspose]
    rfl
  have hs : ∃ g : Representation.IntertwiningMap ρ
      (cyclic (wordRep n (α.colLen 0 * α.colLen 0)) (F (columnSquareWord T))).toRepresentation,
        g ≠ 0 := by
    rw [hF]
    exact ⟨f,hf⟩
  obtain ⟨f',hf'⟩ := hs
  obtain ⟨f'',hf''⟩ := cyclic_projection_support F (columnSquareWord T) f' hf'
  obtain ⟨A,hA⟩ := square_cyclic_embeds_sign_rowColumn (transposeTableau t)
  let B := signTwistMap (rowColumnTransposeCyclicMap t)
  refine ⟨B.comp (A.comp f''), intertwining_comp_ne_zero B ?_ _
    (intertwining_comp_ne_zero A hA f'' hf'')⟩
  exact rowColumnTransposeCyclicMap_injective t

lemma transposeTableau_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    tableauMove (transposeTableau s) (transposeTableau t) = tableauMove s t := by
  ext i
  rfl

lemma rowColumnWord_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    wordRep n _ (tableauMove s t) (rowColumnWord s) = rowColumnWord t := by
  unfold rowColumnWord
  rw [← wordTensor_equivariant]
  change wordTensor _ _ _ (wordRep _ _ (tableauMove s t) (polytabloid (transposeTableau s))
    ⊗ₜ[ℂ] wordRep _ _ (tableauMove s t) (polytabloid s)) = _
  rw [← polytabloid_move s t, ← transposeTableau_move s t,
    ← polytabloid_move (transposeTableau s) (transposeTableau t)]

lemma cyclic_translate_eq {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (g : G) (v : X) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic _ _))
  · apply (cyclic_le _ _ _).mpr
    have h := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic _ _)
    change v ∈ (cyclic ρ (ρ g v)).toSubmodule
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h

lemma rowColumnCyclic_tableau_independent {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    rowColumnCyclic s = rowColumnCyclic t := by
  unfold rowColumnCyclic
  rw [← rowColumnWord_move s t, cyclic_translate_eq]

theorem rowColumn_support_change_tableau {n : ℕ} {α : YoungDiagram} (s t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic s).toRepresentation))
    (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  rw [← rowColumnCyclic_tableau_independent s t]
  exact ⟨f,hf⟩

namespace ShortColumns

theorem even_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (evenTableau b)).toRepresentation, F ≠ 0 := by
  let F := pairWordMap (n := 2*b) (letterLift (Fin.castLE (height_le b 0)))
    (letterLift (Fin.castLE (height_le b 0)))
  have hF : F (columnSquareWord (evenTableau b)) =
      pairFormTensor (pairSplit b) shortPairForm := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, evenTableau_polytabloid, even_square]
  have hs := even_rows_shortPair_support (pairSplit b) μ t he hd
  rw [← hF] at hs
  obtain ⟨g,hg⟩ := hs
  exact cyclic_projection_support F (columnSquareWord (evenTableau b)) g hg

theorem odd_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (oddTableau b)).toRepresentation, F ≠ 0 := by
  let F := pairWordMap (n := 2*b+1) (letterLift (Fin.castLE (height_le b 1)))
    (letterLift (Fin.castLE (height_le b 1)))
  have hF : F (columnSquareWord (oddTableau b)) =
      pairSingletonTensor (oddSplit b) (pairSplit b) shortPairForm (Pi.single 0 1) := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, oddTableau_polytabloid, odd_square]
  have hs := one_odd_row_shortPair_support (oddSplit b) (pairSplit b) μ t k hk he hd
  rw [← hF] at hs
  obtain ⟨g,hg⟩ := hs
  exact cyclic_projection_support F (columnSquareWord (oddTableau b)) g hg

theorem one_extra_even (b : ℕ) (s : Tableau (2*b) (shape b 0))
    (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  obtain ⟨f,hf⟩ := even_columnSquare_support b μ t he hd
  obtain ⟨g,hg⟩ := sign_rowColumn_support_of_columnSquare (evenTableau b) (spechtRep t) f hf
  exact rowColumn_support_change_tableau (evenTableau b) s (spechtRep t) g hg

theorem one_extra_odd (b : ℕ) (s : Tableau (2*b+1) (shape b 1))
    (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  obtain ⟨f,hf⟩ := odd_columnSquare_support b μ t k hk he hd
  obtain ⟨g,hg⟩ := sign_rowColumn_support_of_columnSquare (oddTableau b) (spechtRep t) f hf
  exact rowColumn_support_change_tableau (oddTableau b) s (spechtRep t) g hg

def RowParity (δ : ℕ) (μ : YoungDiagram) : Prop :=
  if δ = 0 then ∀ i, Even (μ.rowLen i)
  else ∃ k, Odd (μ.rowLen k) ∧ ∀ l, l ≠ k → Even (μ.rowLen l)

theorem one_extra (b δ : ℕ) (hδ : δ ≤ 1) (s : Tableau (2*b+δ) (shape b δ))
    (μ : YoungDiagram) (t : Tableau (2*b+δ) μ) (hp : RowParity δ μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  have h : δ = 0 ∨ δ = 1 := by omega
  rcases h with rfl | rfl
  · simp only [RowParity, ↓reduceIte] at hp
    exact one_extra_even b s μ t hp hd
  · simp only [RowParity, Nat.one_ne_zero, ↓reduceIte] at hp
    obtain ⟨k,hk,he⟩ := hp
    exact one_extra_odd b s μ t k hk he hd

end ShortColumns
end Saxl
end
end

end OAI
