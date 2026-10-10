import OAI.RepresentationTheory.Saxl.StripSupport

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
def rowPrefix (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

def Dominates (μ ν : YoungDiagram) : Prop := ∀ k, rowPrefix ν k ≤ rowPrefix μ k

lemma rowLen_zero_of_height_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

lemma rowPrefix_eq_card (μ : YoungDiagram) {k : ℕ} (hk : μ.colLen 0 ≤ k) :
    rowPrefix μ k = μ.card := by
  have he : μ.card = ∑ i : Fin (μ.colLen 0), μ.rowLen i := by
    have hh := Fintype.card_congr (rowCellEquiv μ)
    simpa using hh
  rw [he, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hik hin
  exact rowLen_zero_of_height_le μ (by simpa using hin)

/- Tallest-column bottom deletion, expressed by interlacing rows. -/
def stripRow (μ : YoungDiagram) (t i : ℕ) := μ.rowLen i - t + min t (μ.rowLen (i+1))

lemma stripRow_bounds (μ : YoungDiagram) (t i : ℕ) :
    μ.rowLen (i+1) ≤ stripRow μ t i ∧ stripRow μ t i ≤ μ.rowLen i := by
  have h := μ.rowLen_anti i (i+1) (by omega)
  dsimp [stripRow]
  omega

lemma stripRow_antitone (μ : YoungDiagram) (t : ℕ) : Antitone (stripRow μ t) := by
  intro i j hij
  exact Nat.add_le_add (Nat.sub_le_sub_right (μ.rowLen_anti i j hij) t)
    (min_le_min_left t (μ.rowLen_anti (i+1) (j+1) (by omega)))

def stripRemove (μ : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.2 < stripRow μ t x.1)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1,
      lt_of_le_of_lt hxy.2 (lt_of_lt_of_le hy.2 (stripRow_antitone μ t hxy.1))⟩

@[simp] lemma mem_stripRemove {μ : YoungDiagram} {t i j : ℕ} :
    (i,j) ∈ stripRemove μ t ↔ j < stripRow μ t i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le h (stripRow_bounds μ t i).2), h⟩⟩

@[simp] lemma stripRemove_rowLen (μ : YoungDiagram) (t i : ℕ) :
    (stripRemove μ t).rowLen i = stripRow μ t i := by
  have hh : ∀ j, j < (stripRemove μ t).rowLen i ↔ j < stripRow μ t i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_stripRemove]
  have h₁ := hh ((stripRemove μ t).rowLen i)
  have h₂ := hh (stripRow μ t i)
  omega

lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by
  refine ⟨stripRemove_le μ t, ?_⟩
  intro x hx hxn y hy hyn hcol
  have hhx := YoungDiagram.mem_iff_lt_rowLen.mp hx
  have hhy := YoungDiagram.mem_iff_lt_rowLen.mp hy
  have hnx : stripRow μ t x.1 ≤ x.2 := le_of_not_gt (fun h => hxn (mem_stripRemove.mpr h))
  have hny : stripRow μ t y.1 ≤ y.2 := le_of_not_gt (fun h => hyn (mem_stripRemove.mpr h))
  have hr : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hh := μ.rowLen_anti (x.1+1) y.1 (by omega)
      have hb := (stripRow_bounds μ t x.1).1
      omega
    · exact hr
    · have hh := μ.rowLen_anti (y.1+1) x.1 (by omega)
      have hb := (stripRow_bounds μ t y.1).1
      omega
  exact Prod.ext hr hcol

lemma stripRemove_prefix (μ : YoungDiagram) (t k : ℕ) :
    rowPrefix (stripRemove μ t) k + min t (μ.rowLen 0) =
      rowPrefix μ k + min t (μ.rowLen k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    have hr : (stripRemove μ t).rowLen k + min t (μ.rowLen k) =
        μ.rowLen k + min t (μ.rowLen (k+1)) := by
      rw [stripRemove_rowLen]
      dsimp [stripRow]
      omega
    simp only [rowPrefix, Finset.sum_range_succ] at ih ⊢
    omega

lemma stripRemove_card (μ : YoungDiagram) (t : ℕ) :
    (stripRemove μ t).card + min t (μ.rowLen 0) = μ.card := by
  have hh := stripRemove_prefix μ t (μ.colLen 0)
  rw [rowPrefix_eq_card μ le_rfl, rowLen_zero_of_height_le μ le_rfl, min_zero, add_zero] at hh
  have ht : (stripRemove μ t).colLen 0 ≤ μ.colLen 0 := by
    by_contra h
    have hm : (μ.colLen 0, 0) ∈ stripRemove μ t := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_colLen.mp (stripRemove_le μ t hm)
    omega
  rwa [rowPrefix_eq_card _ ht] at hh

lemma stripRemove_full (μ : YoungDiagram) (i : ℕ) :
    (stripRemove μ (μ.rowLen 0)).rowLen i = μ.rowLen (i+1) := by
  rw [stripRemove_rowLen]
  have hi := μ.rowLen_anti 0 i (Nat.zero_le _)
  have hs := μ.rowLen_anti 0 (i+1) (Nat.zero_le _)
  dsimp [stripRow]
  omega


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

def rowTruncate (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun x => x.1 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.up_left_mem hxy.1 hxy.2 hy.1, lt_of_le_of_lt hxy.1 hy.2⟩

@[simp] lemma mem_rowTruncate {μ : YoungDiagram} {k i j : ℕ} :
    (i,j) ∈ rowTruncate μ k ↔ (i,j) ∈ μ ∧ i < k := by
  change (i,j) ∈ μ.cells.filter (fun x => x.1 < k) ↔ (i,j) ∈ μ.cells ∧ i < k
  exact Finset.mem_filter

lemma rowTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (rowTruncate μ k).rowLen i = if i < k then μ.rowLen i else 0 := by
  have hh : ∀ j, j < (rowTruncate μ k).rowLen i ↔ j < if i < k then μ.rowLen i else 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rowTruncate, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs <;> simp_all
  have h₁ := hh ((rowTruncate μ k).rowLen i)
  have h₂ := hh (if i < k then μ.rowLen i else 0)
  omega

lemma rowTruncate_height (μ : YoungDiagram) (k : ℕ) : (rowTruncate μ k).colLen 0 ≤ k := by
  by_contra h
  have hm : (k,0) ∈ rowTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  exact Nat.lt_irrefl k (mem_rowTruncate.mp hm).2

lemma rowTruncate_prefix (μ : YoungDiagram) (k q : ℕ) (hq : q ≤ k) :
    rowPrefix (rowTruncate μ k) q = rowPrefix μ q := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [rowTruncate_rowLen, ite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hi) hq)]

lemma rowTruncate_card (μ : YoungDiagram) (k : ℕ) :
    (rowTruncate μ k).card = rowPrefix μ k := by
  rw [← rowPrefix_eq_card _ (rowTruncate_height μ k), rowTruncate_prefix _ _ _ le_rfl]

lemma dominates_stripRemove_last (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k+1) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card ∧
      Dominates (stripRemove τ (θ.rowLen k)) (rowTruncate θ k) := by
  have hw : θ.rowLen k ≤ τ.rowLen 0 := by
    have hh := hd 1
    simp only [rowPrefix, Finset.sum_range_one] at hh
    exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hh
  have hθ : (rowTruncate θ k).card + θ.rowLen k = θ.card := by
    rw [rowTruncate_card, ← rowPrefix_succ, rowPrefix_eq_card θ hh]
  have hτ : (stripRemove τ (θ.rowLen k)).card + θ.rowLen k = τ.card := by
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)
  have hcard : (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card := by omega
  refine ⟨hcard, ?_⟩
  have hsmall (q : ℕ) (hq : q ≤ k) : rowPrefix θ q ≤ rowPrefix (stripRemove τ (θ.rowLen k)) q := by
    have he := stripRemove_prefix τ (θ.rowLen k) q
    rw [min_eq_left hw] at he
    by_cases hr : θ.rowLen k ≤ τ.rowLen q
    · rw [min_eq_left hr] at he
      have hh := hd q
      omega
    · rw [min_eq_right (by omega : τ.rowLen q ≤ θ.rowLen k)] at he
      have hsq := hd (q+1)
      rw [rowPrefix_succ, rowPrefix_succ] at hsq
      have ht := θ.rowLen_anti q k hq
      omega
  intro q
  by_cases hq : q ≤ k
  · rw [rowTruncate_prefix _ _ _ hq]
    exact hsmall q hq
  · have hle := rowPrefix_le_card (rowTruncate θ k) q
    rw [rowTruncate_card] at hle
    exact hle.trans ((hsmall k le_rfl).trans (rowPrefix_mono _ (by omega)))

end Saxl

end

end OAI
