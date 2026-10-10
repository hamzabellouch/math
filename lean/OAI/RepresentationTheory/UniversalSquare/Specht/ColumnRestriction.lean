import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.SplitFlag
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnTensorSplit
import OAI.RepresentationTheory.UniversalSquare.Support.ProductInduction
import OAI.RepresentationTheory.UniversalSquare.Specht.CyclicRestriction

namespace OAI

/-! Column Restriction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns
open Columns

def coordinateFlag {h d : ℕ} (ι : Fin h → Fin d) : ℕ → Fin d → ℂ :=
  fun i => if hi : i < h then Pi.single (ι ⟨i,hi⟩) 1 else 0

lemma wedge_coordinateFlag {r h d : ℕ} (hr : r ≤ h) (ι : Fin h → Fin d) :
    wedge r (coordinateFlag ι) = altWord ⊤ (ι ∘ Fin.castLE hr) := by
  classical
  rw [altWord_inverse_sum]
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin r)))
  let e : (⊤ : Subgroup (Equiv.Perm (Fin r))) ≃ Equiv.Perm (Fin r) :=
    { toFun := Subtype.val
      invFun := fun π => ⟨π, Subgroup.mem_top π⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  symm
  unfold wedge
  apply Fintype.sum_equiv e
  intro π
  change signC π.val • Pi.single ((ι ∘ Fin.castLE hr) ∘ π.val) 1 =
    signC π.val • pure (fun i => coordinateFlag ι (π.val i).val)
  congr 1
  have he : (fun i : Fin r => coordinateFlag ι (π.val i).val) =
      fun i => Pi.single (ι (Fin.castLE hr (π.val i))) 1 := by
    funext i
    exact dite_eq_left (lt_of_lt_of_le (π.val i).isLt hr)
  rw [he, pure_single]
  rfl

lemma column_split_basis_nonzero {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    ∃ N : ℕ → Fin (A+B) → ℂ, dotProduct (wedge (a+b) N)
      (positionProduct finSumFinEquiv.symm
        (wedge a (coordinateFlag (Fin.castAdd B)))
        (wedge b (coordinateFlag (Fin.natAdd A)))) ≠ 0 := by
  classical
  let e : Fin (a+b) ≃ Fin a ⊕ Fin b := finSumFinEquiv.symm
  let w : Fin (a+b) → Fin (A+B) :=
    fun i => finSumFinEquiv (Sum.map (Fin.castLE ha) (Fin.castLE hb) (e i))
  have hw : Function.Injective w := by
    intro i j hij
    apply e.injective
    exact (Sum.map_injective.mpr ⟨Fin.castLE_injective ha, Fin.castLE_injective hb⟩)
      (finSumFinEquiv.injective hij)
  have hQ : ∀ i, (finSumFinEquiv.symm (w i)).isLeft = true ↔ (e i).isLeft = true := by
    intro i
    simp only [w, Equiv.symm_apply_apply]
    cases e i <;> rfl
  obtain ⟨N,hN⟩ := split_column_nonzero e w hw
    (fun j => (finSumFinEquiv.symm j).isLeft = true) hQ
  refine ⟨N, ?_⟩
  have hl : leftWord e w = Fin.castAdd B ∘ Fin.castLE ha := by
    funext i
    simp [leftWord, w]
  have hr : rightWord e w = Fin.natAdd A ∘ Fin.castLE hb := by
    funext i
    simp [rightWord, w]
  rw [wedge_coordinateFlag ha, wedge_coordinateFlag hb]
  rwa [hl,hr] at hN

theorem split_blocks_nonzero (ps : List (ℕ × ℕ)) (A B : ℕ)
    (ha : ∀ p ∈ ps, p.1 ≤ A) (hb : ∀ p ∈ ps, p.2 ≤ B) :
    ∃ N : ℕ → Fin (A+B) → ℂ,
      dotProduct (blocks (ps.map (fun p => p.1+p.2)) N)
        (positionProduct (splitPositions ps)
          (blocks (ps.map Prod.fst) (coordinateFlag (Fin.castAdd B)))
          (blocks (ps.map Prod.snd) (coordinateFlag (Fin.natAdd A)))) ≠ 0 := by
  let v := fun p : ℕ × ℕ =>
    positionProduct finSumFinEquiv.symm
      (wedge p.1 (coordinateFlag (Fin.castAdd B)))
      (wedge p.2 (coordinateFlag (Fin.natAdd A)))
  obtain ⟨L,hL,hp⟩ := common_flag_tensorList (fun p : ℕ × ℕ => p.1+p.2)
    (A+B) v ps (fun p hp => Nat.add_le_add (ha p hp) (hb p hp))
    (fun p hp => column_split_basis_nonzero (ha p hp) (hb p hp))
  refine ⟨fun i a => if hi : i < A+B then L ⟨i,hi⟩ a else 0, ?_⟩
  rw [blocks_eq_tensorList Prod.fst, blocks_eq_tensorList Prod.snd, tensorList_split]
  exact hp

def placedFlagMap {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells) (N : ℕ → Fin d → ℂ) :
    Representation.IntertwiningMap (spechtRep ((enumerate rs).trans e))
      (wordRep rs.sum d) :=
  (wordMap (fun i : Fin (μ.colLen 0) => N i.val)).comp
    (subrepInclusion (spechtSub ((enumerate rs).trans e)))

lemma placed_blocks_in_range {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) : blocks rs N ∈ (placedFlagMap e N).range := by
  refine ⟨⟨polytabloid ((enumerate rs).trans e),mem_cyclic _ _⟩, ?_⟩
  exact mapped_placed e hr hc N

lemma product_in_external_range {n a b d : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin a)) X}
    {σ : Representation ℂ (Equiv.Perm (Fin b)) Y}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap ρ (wordRep a d))
    (G : Representation.IntertwiningMap σ (wordRep b d))
    (x : WordSpace a d) (y : WordSpace b d) (hx : x ∈ F.range) (hy : y ∈ G.range) :
    positionProduct e x y ∈ (externalWordMap e F G).range := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  exact ⟨x ⊗ₜ[ℂ] y,externalWordMap_tmul e F G x y⟩

lemma external_range_restriction_support {n a b d : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} [ρ.IsIrreducible]
    {σ : Representation ℂ (Equiv.Perm (Fin a)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin b)) Z}
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (F : Representation.IntertwiningMap σ (wordRep a d))
    (G : Representation.IntertwiningMap τ (wordRep b d))
    (x : WordSpace a d) (y : WordSpace b d) (hx : x ∈ F.range) (hy : y ∈ G.range)
    (f : Representation.IntertwiningMap ρ
      (cyclic (wordRep n d) (positionProduct e x y)).toRepresentation) (hf : f ≠ 0) :
    ∃ R : Representation.IntertwiningMap (ρ.comp (sumPermHom e))
      (externalTensor σ τ), R ≠ 0 := by
  exact cyclic_restriction_support ρ _ _ (sumPermHom e) (positionProduct e x y)
    (externalWordMap e F G) (product_in_external_range e F G x y hx hy) f hf

lemma placed_pair_support {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (N : ℕ → Fin d → ℂ) (u : WordSpace rs.sum d)
    (hN : dotProduct (blocks rs N) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep ((enumerate rs).trans e))
      (cyclic (wordRep rs.sum d) u).toRepresentation, F ≠ 0 := by
  apply specht_to_cyclic_of_pair ((enumerate rs).trans e)
    (fun i : Fin (μ.colLen 0) => N i.val) u
  rwa [mapped_placed e hr hc N]

theorem column_split_restriction (ps : List (ℕ × ℕ))
    (α β γ : YoungDiagram)
    (ea : Cells (ps.map Prod.fst) ≃ α.cells)
    (eb : Cells (ps.map Prod.snd) ≃ β.cells)
    (et : Cells (ps.map (fun p => p.1+p.2)) ≃ γ.cells)
    (hra : ∀ c, (ea c).val.1 = row c)
    (hrb : ∀ c, (eb c).val.1 = row c)
    (hrt : ∀ c, (et c).val.1 = row c)
    (hca : ∀ c c', (ea c).val.2 = (ea c').val.2 ↔ col c = col c')
    (hcb : ∀ c c', (eb c).val.2 = (eb c').val.2 ↔ col c = col c')
    (hct : ∀ c c', (et c).val.2 = (et c').val.2 ↔ col c = col c')
    (A B : ℕ) (ha : ∀ p ∈ ps, p.1 ≤ A) (hb : ∀ p ∈ ps, p.2 ≤ B) :
    ∃ F : Representation.IntertwiningMap
      ((spechtRep ((enumerate (ps.map (fun p => p.1+p.2))).trans et)).comp
        (sumPermHom (splitPositions ps)))
      (externalTensor (spechtRep ((enumerate (ps.map Prod.fst)).trans ea))
        (spechtRep ((enumerate (ps.map Prod.snd)).trans eb))), F ≠ 0 := by
  let a := (enumerate (ps.map Prod.fst)).trans ea
  let b := (enumerate (ps.map Prod.snd)).trans eb
  let t := (enumerate (ps.map (fun p => p.1+p.2))).trans et
  let Na : ℕ → Fin (A+B) → ℂ := coordinateFlag (Fin.castAdd (n := A) B)
  let Nb : ℕ → Fin (A+B) → ℂ := coordinateFlag (Fin.natAdd (m := B) A)
  let u := positionProduct (splitPositions ps)
    (blocks (ps.map Prod.fst) Na) (blocks (ps.map Prod.snd) Nb)
  obtain ⟨N,hN⟩ := split_blocks_nonzero ps A B ha hb
  obtain ⟨F,hF⟩ := placed_pair_support et hrt hct N u hN
  let := specht_irreducible t
  exact external_range_restriction_support (splitPositions ps)
    (placedFlagMap ea Na) (placedFlagMap eb Nb) _ _
    (placed_blocks_in_range ea hra hca Na) (placed_blocks_in_range eb hrb hcb Nb) F hF

end Saxl.FlagColumns
end
end

end OAI
