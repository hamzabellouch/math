import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceDominance
import OAI.RepresentationTheory.UniversalSquare.Support.ConstrainedRows

namespace OAI

/-! Constrained Diagrams. -/

section

namespace UniversalTensorSquare
open Saxl

def firstBound (n : ℕ) (B : List (ℕ × ℕ)) : ℕ :=
  B.foldr (fun p h => if 0 < p.1 then min p.2 h else h) n

lemma firstBound_sound {n : ℕ} (μ : YoungDiagram) (hc : μ.card = n)
    {B : List (ℕ × ℕ)} (hb : RowBounds μ B) : μ.rowLen 0 ≤ firstBound n B := by
  induction B with
  | nil =>
    have hh := rowPrefix_le_card μ 1
    simpa [firstBound,rowPrefix,hc] using hh
  | cons p B ih =>
    have hp := hb p (by simp)
    simp only [firstBound,List.foldr_cons,ite_eq_left hp.1]
    exact le_min ((rowLen_first_le_prefix μ hp.1).trans hp.2)
      (ih (fun q hq => hb q (by simp [hq])))

lemma clippedSum_rowLens (μ : YoungDiagram) (k : ℕ) :
    clippedSum μ.rowLens k = colPrefix μ k := by
  rw [colPrefix_eq_min_sum]
  rw [YoungDiagram.rowLens]
  simp only [clippedSum,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

def rowsWithin (n : ℕ) (A B : List (ℕ × ℕ)) : List (List ℕ) :=
  (List.range' (minHeight n B) (firstBound n A + 1 - minHeight n B)).flatMap fun h =>
    constrainedRows h n (firstBound n B) A B

lemma rowLens_mem_rowsWithin {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hc : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B) :
    μ.rowLens ∈ rowsWithin n A B := by
  apply List.mem_flatMap.mpr
  refine ⟨μ.rowLens.length,?_,?_⟩
  · have hlo := minHeight_sound hn μ hc hb
    have hhi := firstBound_sound μ.transpose ((transpose_card μ).trans hc) ha
    simp only [YoungDiagram.rowLen_transpose] at hhi
    simp only [List.mem_range'_1,YoungDiagram.length_rowLens]
    omega
  · apply mem_constrainedRows _ _ _ _ _ _ rfl
    · exact (card_eq_sum_rowLens μ).symm.trans hc
    · exact μ.pos_of_mem_rowLens
    · intro a ha'
      obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha'
      rw [← he, YoungDiagram.get_rowLens]
      exact (μ.rowLen_anti _ _ (Nat.zero_le _)).trans (firstBound_sound μ hc hb)
    · exact μ.rowLens_sorted
    · intro p hp
      rw [clippedSum_rowLens]
      exact (ha p hp).2
    · intro p hp
      rw [← rowPrefix_eq_take]
      exact (hb p hp).2

lemma rowsWithin_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hc : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    {P : List ℕ → Prop} (h : ∀ rs ∈ rowsWithin n A B, P rs) : P μ.rowLens :=
  h _ (rowLens_mem_rowsWithin hn μ hc ha hb)

end UniversalTensorSquare
end

end OAI
