import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.PairRun
import OAI.RepresentationTheory.UniversalSquare.Balance.EmptyPacking

namespace OAI

/-! Run Bands. -/

section

noncomputable section
namespace Saxl.Balance

theorem WordPacking.pairRunAny {a m d : ℕ} (ha : 2 ≤ a)
    (hd : a+2*m-1 ≤ d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ k ∈ pairMarks a m, ∀ z,
      (A z ∧ label z = k) ↔ output z ∈ Set.Icc k (k+1)) :
    Nonempty (WordPacking (pairColumns a m) (pairParts a m) d A label (pairMarks a m)) := by
  by_cases hm : m = 0
  · subst m
    simpa [pairColumns,pairParts,pairMarks] using Nonempty.intro (WordPacking.empty d A label)
  · exact WordPacking.pairRun ha (by omega) hd A label he

def runBands (a m q U : ℕ) (hg : a+2*m ≤ q) (hU : q ≤ U) : OutputBands where
  starts := Finset.range a ∪ pairMarks a m ∪ {q}
  upper k := if k = q then U else if k ∈ pairMarks a m then k+1 else k
  nonempty := by
    intro k hk
    split_ifs with h h
    · omega
    · omega
    · omega
  separated := by
    intro k hk l hl hkl
    have hk' : k < a ∨ k ∈ pairMarks a m ∨ k = q := by
      simpa only [Finset.mem_union,Finset.mem_range,Finset.mem_singleton,or_assoc] using hk
    have hl' : l < a ∨ l ∈ pairMarks a m ∨ l = q := by
      simpa only [Finset.mem_union,Finset.mem_range,Finset.mem_singleton,or_assoc] using hl
    have hle : l ≤ q := by
      rcases hl' with h | h | h
      · omega
      · have := pairMarks_bound h; omega
      · omega
    rw [ite_eq_right (by omega)]
    split_ifs with hm
    · have hb := pairMarks_bound hm
      rcases hl' with h | h | h
      · omega
      · exact pairMarks_separated hm h hkl
      · omega
    · exact hkl

lemma runBands_low {a m q U k : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U) (hk : k < a) :
    k ∈ (runBands a m q U hg hU).starts ∧ (runBands a m q U hg hU).upper k = k := by
  constructor
  · apply Finset.mem_union_left
    exact Finset.mem_union_left _ (Finset.mem_range.mpr hk)
  · change (if k=q then U else if k ∈ pairMarks a m then k+1 else k) = k
    have hn : k ∉ pairMarks a m := by
      intro hh
      have := pairMarks_bound hh
      omega
    rw [ite_eq_right (by omega),ite_eq_right hn]

lemma runBands_pair {a m q U k : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U)
    (hk : k ∈ pairMarks a m) :
    k ∈ (runBands a m q U hg hU).starts ∧ (runBands a m q U hg hU).upper k = k+1 := by
  constructor
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hk)
  · have hh := pairMarks_bound hk
    change (if k=q then U else if k ∈ pairMarks a m then k+1 else k) = k+1
    rw [ite_eq_right (by omega),ite_eq_left hk]

lemma runBands_top {a m q U : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U) :
    q ∈ (runBands a m q U hg hU).starts ∧ (runBands a m q U hg hU).upper q = U := by
  constructor
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self q)
  · simp [runBands]

lemma runBands_low_iff {a m q U k d : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U) (hk : k < a)
    (z : Fin (d*d)) :
    ((runBands a m q U hg hU).alphabet d z ∧
      (runBands a m q U hg hU).letterLabel d z = k) ↔ output z = k := by
  rw [(runBands a m q U hg hU).letter_iff (runBands_low hg hU hk).1,
    (runBands_low hg hU hk).2]
  simp only [Set.mem_Icc]
  omega

lemma runBands_pair_iff {a m q U k d : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U)
    (hk : k ∈ pairMarks a m) (z : Fin (d*d)) :
    ((runBands a m q U hg hU).alphabet d z ∧
      (runBands a m q U hg hU).letterLabel d z = k) ↔ output z ∈ Set.Icc k (k+1) := by
  rw [(runBands a m q U hg hU).letter_iff (runBands_pair hg hU hk).1,
    (runBands_pair hg hU hk).2]

lemma runBands_top_iff {a m q U d : ℕ} (hg : a+2*m ≤ q) (hU : q ≤ U)
    (z : Fin (d*d)) :
    ((runBands a m q U hg hU).alphabet d z ∧
      (runBands a m q U hg hU).letterLabel d z = q) ↔ output z ∈ Set.Icc q U := by
  rw [(runBands a m q U hg hU).letter_iff (runBands_top hg hU).1,
    (runBands_top hg hU).2]

end Saxl.Balance
end
end

end OAI
