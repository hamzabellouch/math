import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SymmetricPairs

namespace OAI

/-! Alternate Columns. -/

section

noncomputable section
namespace Saxl

def ceilRows (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.filter (fun c => 2*c.2 < μ.rowLen c.1)
  isLowerSet := by
    intro x y hxy hy
    obtain ⟨hym,hy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨μ.up_left_mem hxy.1 hxy.2 hym, ?_⟩
    have hm := μ.rowLen_anti _ _ hxy.1
    have hj := hxy.2
    omega

lemma mem_ceilRows (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ ceilRows μ ↔ 2*j < μ.rowLen i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),h⟩⟩

lemma ceilRows_rowLen (μ : YoungDiagram) (i : ℕ) :
    (ceilRows μ).rowLen i = (μ.rowLen i + 1) / 2 := by
  have hh : ∀ j, j < (ceilRows μ).rowLen i ↔ j < (μ.rowLen i+1) / 2 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_ceilRows]
    omega
  have h₁ := hh ((ceilRows μ).rowLen i)
  have h₂ := hh ((μ.rowLen i+1) / 2)
  omega

lemma ceilRows_height (μ : YoungDiagram) : (ceilRows μ).colLen 0 = μ.colLen 0 := by
  have hh : ∀ i, i < (ceilRows μ).colLen 0 ↔ i < μ.colLen 0 := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_ceilRows]
    norm_num only [mul_zero]
    rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
  have h₁ := hh ((ceilRows μ).colLen 0)
  have h₂ := hh (μ.colLen 0)
  omega

lemma halfRows_le_ceilRows (μ : YoungDiagram) : halfRows μ ≤ ceilRows μ := by
  intro c hc
  have hl := (mem_halfRows μ c.1 c.2).mp hc
  exact (mem_ceilRows μ c.1 c.2).mpr (by omega)

def alternateCells (μ : YoungDiagram) :
    (ceilRows μ).cells ⊕ (halfRows μ).cells ≃ μ.cells where
  toFun := Sum.elim
    (fun c => ⟨(c.val.1,2*c.val.2), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_ceilRows μ _ _).mp c.property)⟩)
    (fun c => ⟨(c.val.1,2*c.val.2+1), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_halfRows μ _ _).mp c.property)⟩)
  invFun c :=
    if h : c.val.2 % 2 = 0 then Sum.inl ⟨(c.val.1,c.val.2/2), (mem_ceilRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2) < μ.rowLen c.val.1
      omega)⟩
    else Sum.inr ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
  left_inv c := by
    cases c with
    | inl c => simp
    | inr c =>
      simp
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (2*c.val.2+1)/2 = c.val.2
        omega
  right_inv c := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2) = c.val.2
        change c.val.2 % 2 = 0 at h
        omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2)+1 = c.val.2
        change c.val.2 % 2 ≠ 0 at h
        omega

lemma alternateCells_card (μ : YoungDiagram) :
    (ceilRows μ).card + (halfRows μ).card = μ.card := by
  simpa only [Fintype.card_sum, Fintype.card_coe] using Fintype.card_congr (alternateCells μ)

def alternateTableau {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) : Tableau n μ :=
  e.trans ((Equiv.sumCongr s t).trans (alternateCells μ))

lemma alternateTableau_left {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) (i : Fin a) :
    (alternateTableau μ e s t (e.symm (Sum.inl i))).val = ((s i).val.1,2*(s i).val.2) := by
  simp [alternateTableau, alternateCells]

lemma alternateTableau_right {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) (i : Fin b) :
    (alternateTableau μ e s t (e.symm (Sum.inr i))).val = ((t i).val.1,2*(t i).val.2+1) := by
  simp [alternateTableau, alternateCells]

lemma alternateTableau_group_sector {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) :
    columnGroup (alternateTableau μ e s t) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [alternateTableau_left, alternateTableau_right] at hc
    dsimp only at hc
    omega
  · rw [alternateTableau_left, alternateTableau_right] at hc
    dsimp only at hc
    omega

lemma alternateTableau_factor {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) :
    polytabloid (alternateTableau μ e s t) = positionProduct e
      (letterLift (Fin.cast (ceilRows_height μ)) (polytabloid s))
      (letterLift (Fin.cast (ceilRows_height μ) ∘ rowLetterInclusion (halfRows_le_ceilRows μ))
        (polytabloid t)) := by
  let u := alternateTableau μ e s t
  let f : Fin n → ℕ := fun i => (u i).val.2
  have hn : columnGroup u = fiberGroup f := rfl
  have hg : columnGroup u = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (alternateTableau_group_sector μ e s t)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (u (e.symm (Sum.inl (g i)))).val.2 =
      (u (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [u, alternateTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup t := by
    apply Subgroup.ext
    intro g
    change (∀ i, (u (e.symm (Sum.inr (g i)))).val.2 =
      (u (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (t (g i)).val.2 = (t i).val.2
    simp only [u, alternateTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord u) = Fin.cast (ceilRows_height μ) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (u (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [alternateTableau_left]
  have hw₂ : rightWord e (rowWord u) =
      (Fin.cast (ceilRows_height μ) ∘ rowLetterInclusion (halfRows_le_ceilRows μ)) ∘ rowWord t := by
    funext i
    apply Fin.ext
    change (u (e.symm (Sum.inr i))).val.1 = (t i).val.1
    rw [alternateTableau_right]
  change polytabloid u = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← letterLift_altWord, ← polytabloid_eq_altWord,
    ← polytabloid_eq_altWord]

lemma alternateRows_difference (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) (c : ℕ × ℕ) :
    c ∈ ceilRows μ ∧ c ∉ halfRows μ ↔ c = (k, μ.rowLen k / 2) := by
  rw [mem_ceilRows, mem_halfRows]
  constructor
  · rintro ⟨hc,hc'⟩
    have hck : c.1 = k := by
      by_contra hn
      obtain ⟨q,hq⟩ := he c.1 hn
      omega
    obtain ⟨q,hq⟩ := hk
    apply Prod.ext
    · exact hck
    · dsimp
      simp only [hck] at hc hc'
      omega
  · rintro rfl
    obtain ⟨q,hq⟩ := hk
    dsimp
    omega

lemma alternateRows_strip (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) :
    HorizontalStrip (halfRows μ) (ceilRows μ) := by
  refine ⟨halfRows_le_ceilRows μ, ?_⟩
  intro x hx hx' y hy hy' hxy
  exact ((alternateRows_difference μ k hk he x).mp ⟨hx,hx'⟩).trans
    ((alternateRows_difference μ k hk he y).mp ⟨hy,hy'⟩).symm

end Saxl
end
end

end OAI
