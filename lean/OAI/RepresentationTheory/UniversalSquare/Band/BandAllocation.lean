import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.Capacity

namespace OAI

/-! Band Allocation. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def prefixFill (f : ℕ → ℕ) (r i : ℕ) : ℕ :=
  min (f i) (r - ∑ j ∈ Finset.range i, f j)

lemma prefixFill_le (f : ℕ → ℕ) (r i : ℕ) : prefixFill f r i ≤ f i := min_le_left _ _

lemma prefixFill_antitone {f : ℕ → ℕ} (hf : Antitone f) (r : ℕ) :
    Antitone (prefixFill f r) := by
  intro i j hij
  apply min_le_min (hf hij)
  apply Nat.sub_le_sub_left
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

lemma prefixFill_sum (f : ℕ → ℕ) (r k : ℕ) :
    (∑ i ∈ Finset.range k, prefixFill f r i) = min r (∑ i ∈ Finset.range k, f i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, prefixFill]
    omega

def columnCut (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f) : YoungDiagram where
  cells := μ.cells.filter (fun c => c.1 < f c.2)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.isLowerSet hxy hy.1, hxy.1.trans_lt (hy.2.trans_le (hf hxy.2))⟩

lemma columnCut_le (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f) :
    columnCut μ f hf ≤ μ := fun _ h => (Finset.mem_filter.mp h).1

lemma columnCut_colLen (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f)
    (hb : ∀ i, f i ≤ μ.colLen i) (i : ℕ) : (columnCut μ f hf).colLen i = f i := by
  have H (j : ℕ) : j < (columnCut μ f hf).colLen i ↔ j < f i := by
    rw [← YoungDiagram.mem_iff_lt_colLen]
    change ((j,i) ∈ μ.cells.filter _) ↔ _
    simp only [Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_colLen.mpr (h.trans_le (hb i)),h⟩⟩
  have h₁ := H ((columnCut μ f hf).colLen i)
  have h₂ := H (f i)
  omega

lemma columnCut_card (μ : YoungDiagram) (f : ℕ → ℕ) (hf : Antitone f)
    (hb : ∀ i, f i ≤ μ.colLen i) :
    (columnCut μ f hf).card = ∑ i ∈ Finset.range (μ.rowLen 0), f i := by
  have hw : (columnCut μ f hf).rowLen 0 ≤ μ.rowLen 0 := by
    by_contra hh
    have he := columnCut_le μ f hf (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hh))
    exact Nat.lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp he)
  rw [← transpose_card, ← rowPrefix_eq_card _ (by simpa using hw)]
  simp only [rowPrefix, YoungDiagram.rowLen_transpose, columnCut_colLen μ f hf hb]

def extraCapacity (μ : YoungDiagram) (d q i : ℕ) : ℕ :=
  if i < q then (μ.colLen i-d)/2 else 0

lemma extraCapacity_antitone (μ : YoungDiagram) (d q : ℕ) :
    Antitone (extraCapacity μ d q) := by
  intro i j hij
  dsimp only [extraCapacity]
  split_ifs with hj hi hi
  · exact Nat.div_le_div_right (Nat.sub_le_sub_right (μ.colLen_anti i j hij) d)
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

lemma extraCapacity_sum (μ : YoungDiagram) (d q : ℕ) :
    (∑ i ∈ Finset.range (μ.rowLen 0), extraCapacity μ d q i) = bandCapacity μ d q := by
  classical
  have hs : ∀ i, μ.rowLen 0 ≤ i → μ.colLen i = 0 := by
    intro i hi
    simpa only [YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] using
      rowLen_zero_of_height_le μ.transpose (by simpa using hi)
  unfold bandCapacity
  by_cases hq : q ≤ μ.rowLen 0
  · rw [← Finset.sum_subset (Finset.range_mono hq) (by
      intro i hi hni
      simp only [Finset.mem_range] at hni
      simp [extraCapacity, hni])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [extraCapacity, Finset.mem_range.mp hi, ite_true]
  · have hh : μ.rowLen 0 ≤ q := by omega
    rw [← Finset.sum_subset (Finset.range_mono hh) (by
      intro i hi hni
      simp only [Finset.mem_range, not_lt] at hni
      simp only [hs i hni, Nat.zero_sub, Nat.zero_div])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [extraCapacity, (Finset.mem_range.mp hi).trans_le hh, ite_true]

lemma pathCapacity_sum (μ : YoungDiagram) (d : ℕ) :
    (∑ i ∈ Finset.range (μ.rowLen 0), min d (μ.colLen i)) = rowPrefix μ d := by
  rw [← rowTruncate_card, ← transpose_card]
  have hw : (rowTruncate μ d).rowLen 0 ≤ μ.rowLen 0 := by
    rw [rowTruncate_rowLen]
    split_ifs <;> omega
  rw [← rowPrefix_eq_card _ (by simpa using hw)]
  simp only [rowPrefix, YoungDiagram.rowLen_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Nat.le_antisymm
  · by_contra hn
    have hh : ((rowTruncate μ d).colLen i,i) ∈ rowTruncate μ d :=
      mem_rowTruncate.mpr ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by omega), by omega⟩
    exact Nat.lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp hh)
  · by_contra hn
    have hh : (min d (μ.colLen i),i) ∈ rowTruncate μ d :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have ht := mem_rowTruncate.mp hh
    have hc := YoungDiagram.mem_iff_lt_colLen.mp ht.1
    omega

theorem band_subdiagram_allocation (lam : YoungDiagram) (K r d q : ℕ)
    (hK : K ≤ rowPrefix lam d) (hclear : d*q+7+d ≤ K)
    (hr : r ≤ bandCapacity lam d q) :
    ∃ π η μ : YoungDiagram,
      μ ≤ lam ∧ π.card = K ∧ η.card = 2*r ∧ μ.card = K+2*r ∧
      (∀ i, μ.colLen i = π.colLen i + η.colLen i) ∧
      (∀ i, π.colLen i ≤ d) ∧
      (∀ i, Even (η.colLen i)) ∧ η.rowLen 0 ≤ q ∧
      (∀ i, 0 < η.colLen i → π.colLen i = d) := by
  let p := prefixFill (fun i => min d (lam.colLen i)) K
  let e := fun i => 2*prefixFill (extraCapacity lam d q) r i
  have hpanti : Antitone p := prefixFill_antitone (fun _ _ h => min_le_min le_rfl (lam.colLen_anti _ _ h)) K
  have heanti : Antitone e := fun _ _ h => Nat.mul_le_mul_left 2
    (prefixFill_antitone (extraCapacity_antitone lam d q) r h)
  have hpbound (i : ℕ) : p i ≤ min d (lam.colLen i) := prefixFill_le _ _ _
  have hebound (i : ℕ) : e i ≤ lam.colLen i-d := by
    have hh := Nat.mul_le_mul_left 2 (prefixFill_le (extraCapacity lam d q) r i)
    have hc : extraCapacity lam d q i ≤ (lam.colLen i-d)/2 := by
      dsimp [extraCapacity]
      split_ifs <;> omega
    dsimp only [e]
    omega
  have hpb (i : ℕ) : p i ≤ lam.colLen i := (hpbound i).trans (min_le_right _ _)
  have heb (i : ℕ) : e i ≤ lam.colLen i := (hebound i).trans (Nat.sub_le _ _)
  have hpos (i : ℕ) (hi : 0 < e i) : i < q ∧ d ≤ lam.colLen i := by
    have hh := prefixFill_le (extraCapacity lam d q) r i
    have hc : 0 < extraCapacity lam d q i := by dsimp [e] at hi; omega
    dsimp only [extraCapacity] at hc
    split_ifs at hc with h
    · exact ⟨h, by omega⟩
    · omega
  have hsbound (i : ℕ) : p i+e i ≤ lam.colLen i := by
    by_cases hi : 0 < e i
    · have hh := (hpos i hi).2
      have hp := (hpbound i).trans (min_le_left _ _)
      have he := hebound i
      omega
    · have hp := hpb i
      omega
  let π := columnCut lam p hpanti
  let η := columnCut lam e heanti
  let μ := columnCut lam (fun i => p i+e i) (fun _ _ h => Nat.add_le_add (hpanti h) (heanti h))
  have hπ (i) : π.colLen i = p i := columnCut_colLen _ _ _ hpb i
  have hη (i) : η.colLen i = e i := columnCut_colLen _ _ _ heb i
  have hμ (i) : μ.colLen i = p i+e i := columnCut_colLen _ _ _ hsbound i
  have hpSum : (∑ i ∈ Finset.range (lam.rowLen 0), p i) = K := by
    rw [prefixFill_sum, pathCapacity_sum, min_eq_left hK]
  have heSum : (∑ i ∈ Finset.range (lam.rowLen 0), e i) = 2*r := by
    rw [← Finset.mul_sum, prefixFill_sum, extraCapacity_sum, min_eq_left hr]
  refine ⟨π,η,μ,columnCut_le _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (columnCut_card _ _ _ hpb).trans hpSum
  · exact (columnCut_card _ _ _ heb).trans heSum
  · refine (columnCut_card lam (fun i => p i+e i)
      (fun _ _ h => Nat.add_le_add (hpanti h) (heanti h)) hsbound).trans ?_
    rw [Finset.sum_add_distrib, hpSum, heSum]
  · intro i
    rw [hμ,hπ,hη]
  · intro i
    exact (hπ i).le.trans ((hpbound i).trans (min_le_left _ _))
  · intro i
    rw [hη]
    exact even_two_mul _
  · by_contra hh
    have h : 0 < η.colLen q := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.lt_of_not_ge hh))
    rw [hη] at h
    exact Nat.lt_irrefl _ (hpos q h).1
  · intro i hi
    rw [hπ]
    rw [hη] at hi
    obtain ⟨hiq,hid⟩ := hpos i hi
    have hs : (∑ j ∈ Finset.range i, min d (lam.colLen j)) ≤ i*d := by
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using
        (Finset.sum_le_sum (s := Finset.range i) (fun j _ => min_le_left d (lam.colLen j)))
    have hmul : (i+1)*d ≤ q*d := Nat.mul_le_mul_right d hiq
    dsimp only [p, prefixFill]
    rw [min_eq_left hid]
    apply min_eq_left
    apply Nat.le_sub_of_add_le
    have hc : q*d ≤ K := by simpa only [Nat.mul_comm] using (show d*q ≤ K by omega)
    calc d + (∑ j ∈ Finset.range i, min d (lam.colLen j)) ≤ d+i*d := Nat.add_le_add_left hs _
      _ = (i+1)*d := by ring
      _ ≤ q*d := hmul
      _ ≤ K := hc

end UniversalTensorSquare
end
end

end OAI
