import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.RefinedCapacity

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def RowBounds (μ : YoungDiagram) (B : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ B, 0 < p.1 ∧ rowPrefix μ p.1 ≤ p.2

def minHeight (n : ℕ) (B : List (ℕ × ℕ)) : ℕ :=
  B.foldr (fun p h => if p.2 < n then max (p.1+1) h else h) 1

lemma minHeight_pos (n : ℕ) (B : List (ℕ × ℕ)) : 0 < minHeight n B := by
  induction B with
  | nil => simp [minHeight]
  | cons p B ih =>
    simp only [minHeight,List.foldr_cons]
    split_ifs
    · exact lt_of_lt_of_le ih (le_max_right _ _)
    · exact ih

lemma minHeight_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {B : List (ℕ × ℕ)} (hb : RowBounds μ B) :
    minHeight n B ≤ μ.colLen 0 := by
  have hpos : 0 < μ.colLen 0 := by
    have hc := rowPrefix_eq_card μ (k := 0)
    by_contra h
    have hz := hc (by omega)
    simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hz
    omega
  induction B with
  | nil => exact hpos
  | cons p B ih =>
    have hp := hb p (by simp)
    have htail : RowBounds μ B := fun q hq => hb q (by simp [hq])
    simp only [minHeight,List.foldr_cons]
    split_ifs with hh
    · apply max_le _ (ih htail)
      by_contra h
      have := rowPrefix_eq_card μ (show μ.colLen 0 ≤ p.1 by omega)
      omega
    · exact ih htail

lemma rowLen_first_le_prefix (μ : YoungDiagram) {i : ℕ} (hi : 0 < i) :
    μ.rowLen 0 ≤ rowPrefix μ i := by
  have h := rowPrefix_mono μ (show 1 ≤ i from hi)
  simpa [rowPrefix] using h

def impossibleBounds (n : ℕ) (A B : List (ℕ × ℕ)) : Prop :=
  (∃ p ∈ A, p.2 < minHeight n B) ∨
  (∃ q ∈ B, q.2 < minHeight n A) ∨
  ∃ p ∈ A, ∃ q ∈ B,
    refinedArea p.1 q.1 p.2 q.2
      (endpointBound p.1 p.2 (minHeight n B))
      (endpointBound q.1 q.2 (minHeight n A))
      (minHeight n B) (minHeight n A) < n

instance (n : ℕ) (A B : List (ℕ × ℕ)) : Decidable (impossibleBounds n A B) :=
  inferInstanceAs (Decidable ((∃ p ∈ A, p.2 < minHeight n B) ∨
    (∃ q ∈ B, q.2 < minHeight n A) ∨
    ∃ p ∈ A, ∃ q ∈ B, refinedArea p.1 q.1 p.2 q.2
      (endpointBound p.1 p.2 (minHeight n B))
      (endpointBound q.1 q.2 (minHeight n A))
      (minHeight n B) (minHeight n A) < n))

lemma impossibleBounds_false {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    (h : impossibleBounds n A B) : False := by
  have hH := minHeight_sound hn μ hcard hb
  have hW := minHeight_sound hn μ.transpose ((transpose_card _).trans hcard) ha
  simp only [YoungDiagram.colLen_transpose] at hW
  rcases h with ⟨p,hp,h⟩ | ⟨q,hq,h⟩ | ⟨p,hp,q,hq,h⟩
  · have hs := (rowLen_first_le_prefix μ.transpose (ha p hp).1).trans (ha p hp).2
    simp only [YoungDiagram.rowLen_transpose] at hs
    omega
  · have hs := (rowLen_first_le_prefix μ (hb q hq).1).trans (hb q hq).2
    omega
  · have hX := endpointBound_sound μ.transpose (ha p hp).1 (ha p hp).2
      (show minHeight n B ≤ μ.transpose.rowLen 0 by simpa using hH)
    have hY := endpointBound_sound μ (hb q hq).1 (hb q hq).2 hW
    have ht := area_le_refined μ (ha p hp).1 (hb q hq).1 (ha p hp).2
      (hb q hq).2 (by simpa using hX) hY hH hW (minHeight_pos n B) (minHeight_pos n A)
    omega

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

lemma not_dominates_witness {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : ¬ Dominates μ θ) :
    ∃ k, 1 ≤ k ∧ k ≤ θ.colLen 0 ∧ rowPrefix μ k < rowPrefix θ k := by
  classical
  obtain ⟨k,hk⟩ := not_forall.mp h
  have hk' : rowPrefix μ k < rowPrefix θ k := Nat.lt_of_not_ge hk
  by_cases hb : k ≤ θ.colLen 0
  · refine ⟨k,?_,hb,hk'⟩
    by_contra ht
    have hz : k = 0 := by omega
    simp [hz,rowPrefix] at hk'
  · refine ⟨θ.colLen 0,?_,le_rfl,?_⟩
    · by_contra ht
      have hz : θ.colLen 0 = 0 := by omega
      have hs := rowPrefix_eq_card θ (le_of_eq hz)
      simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hs
      have hu := rowPrefix_le_card θ k
      omega
    · have hle := rowPrefix_mono μ (show θ.colLen 0 ≤ k by omega)
      rw [rowPrefix_eq_card θ (by omega), ← hc] at hk'
      rw [rowPrefix_eq_card θ le_rfl, ← hc]
      omega

def coreImpossible (K d : ℕ) (A : List (ℕ × ℕ)) : Prop :=
    ∃ p ∈ A, d ≤ p.1 ∧ p.2 < K

instance (K d : ℕ) (A : List (ℕ × ℕ)) : Decidable (coreImpossible K d A) :=
  inferInstanceAs (Decidable (∃ p ∈ A, d ≤ p.1 ∧ p.2 < K))

lemma coreImpossible_false (μ : YoungDiagram) {K d : ℕ}
    (hd : K ≤ rowPrefix μ d) {A : List (ℕ × ℕ)} (ha : RowBounds μ A)
    (h : coreImpossible K d A) : False := by
  obtain ⟨p,hp,hpd,hpK⟩ := h
  have hle := (hd.trans (rowPrefix_mono μ hpd)).trans (ha p hp).2
  omega

def refinedCheck (n M r d e a b : ℕ) (q : List ℕ) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  coreImpossible (2*M-1) d A ∨ coreImpossible (2*M-1) e B ∨ impossibleBounds n A B

instance (n M r d e a b : ℕ) (q : List ℕ) : Decidable (refinedCheck n M r d e a b q) := by
  unfold refinedCheck; infer_instance

theorem refined_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 9 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (check : ∀ d ∈ List.range 4, ∀ e ∈ List.range 4,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        refinedCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens) :
    colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2 ∨
      BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨ Dominates μ.transpose θ := by
  classical
  by_contra hh
  push Not at hh
  rcases hh with ⟨hfour,hfour',hband,hband',hdom,hdom'⟩
  have hK : 0 < 2*M-1 := by omega
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := first_prefix_height μ.transpose hK (by unfold colPrefix at hfour; omega)
  obtain ⟨e,he,he',hWe,hWe'⟩ := first_prefix_height μ hK (by
    simp only [colPrefix,YoungDiagram.transpose_transpose] at hfour'; omega)
  obtain ⟨a,ha,ha',hA⟩ := not_dominates_witness ((transpose_card _).trans hc |>.trans ht.symm) hdom'
  obtain ⟨b,hb,hb',hB⟩ := not_dominates_witness (hc.trans ht.symm) hdom
  have hAf := prefixBounds_sound μ hM hr hHd' hWe hband
  have hBf := prefixBounds_sound μ.transpose hM hr
    (by simpa only [colPrefix,YoungDiagram.transpose_transpose] using hWe') hHd hband'
  let A := prefixBounds M r d e ++ [(a,(θ.rowLens.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(θ.rowLens.take b).sum-1)]
  have hAbb : RowBounds μ.transpose A := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAf p hp
    · have heq : p = (a,(θ.rowLens.take a).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hA
      exact ⟨ha,by dsimp; omega⟩
  have hBbb : RowBounds μ B := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simpa only [colPrefix,YoungDiagram.transpose_transpose] using hBf p hp
    · have heq : p = (b,(θ.rowLens.take b).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hB
      exact ⟨hb,by dsimp; omega⟩
  have h := check (d-1) (by simp; omega) (e-1) (by simp; omega)
    (a-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    (b-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  have hde : d-1+1 = d := by omega
  have hee : e-1+1 = e := by omega
  have hae : a-1+1 = a := by omega
  have hbe : b-1+1 = b := by omega
  rw [hde,hee,hae,hbe] at h
  rcases h with h | h | h
  · exact coreImpossible_false μ.transpose hHd hAbb h
  · exact coreImpossible_false μ hWe hBbb h
  · exact impossibleBounds_false hn μ hc hAbb hBbb h

end UniversalTensorSquare
end
end

end OAI
