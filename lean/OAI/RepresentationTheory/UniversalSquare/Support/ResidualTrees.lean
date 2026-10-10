import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.RegionExhaustion

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

inductive RowTree where
  | empty
  | node (key : List ℕ) (left right : RowTree)
  deriving DecidableEq

namespace RowTree

def find (rs : List ℕ) : RowTree → Bool
  | .empty => false
  | .node key l r => if rs = key then true else if compare rs key = Ordering.lt
      then l.find rs else r.find rs

def All (P : List ℕ → Prop) : RowTree → Prop
  | .empty => True
  | .node key l r => P key ∧ l.All P ∧ r.All P

lemma find_sound {P : List ℕ → Prop} {t : RowTree} (h : t.All P)
    {rs : List ℕ} (hf : t.find rs = true) : P rs := by
  induction t with
  | empty => simp [find] at hf
  | node key l r hl hr =>
    simp only [find] at hf
    obtain ⟨hk,hL,hR⟩ := h
    split_ifs at hf with he hc
    · simpa only [he] using hk
    · exact hl hL hf
    · exact hr hR hf

end RowTree

def TreeResidual (M r : ℕ) (qs : List (List ℕ)) (t : RowTree) (rs : List ℕ) : Prop :=
  ResidualProperty M r qs [] rs ∨ t.find rs = true ∨ t.find (transposeRows rs) = true
instance (M r : ℕ) (qs : List (List ℕ)) (t : RowTree) :
    DecidablePred (TreeResidual M r qs t) := by
  intro rs; unfold TreeResidual; infer_instance

lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs : List (List ℕ)} {t : RowTree}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  rcases h with h | h | h
  · exact residualProperty_sound hM hδ hn hre hcones (by simp) hgood hsum h
  · exact RowTree.find_sound htree h
  · have hh := RowTree.find_sound htree h
    rw [rowDiagram_transposeRows hgood] at hh
    simpa only [YoungDiagram.transpose_transpose] using
      hh.target_transpose (candidate_transpose M b δ)

lemma rowDiagram_candidate {M b δ : ℕ} (hM : 4 ≤ M) :
    rowDiagram ([M+b+δ,M-1+b] ++ (List.range' 3 (M-4)).reverse ++
      List.replicate (b+1) 2 ++ List.replicate (1+δ) 1) = candidate M b δ := by
  rw [← candidate_rowLens hM, rowDiagram_rowLens]

end UniversalTensorSquare
end
end

end OAI
