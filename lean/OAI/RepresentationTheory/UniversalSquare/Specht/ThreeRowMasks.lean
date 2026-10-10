import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.FiniteDiagrams
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowProjected
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingCone

namespace OAI

/-! Three Row Masks. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

structure ThreeRowEntry where
  core : List ℕ
  middle : List ℕ
  final : List ℕ
  deriving DecidableEq

namespace ThreeRowEntry

def Valid (m s : ℕ) (c : ThreeRowEntry) : Prop :=
  c.core.length ≤ 3 ∧ c.final.length ≤ 3 ∧
  c.core.sum = 2*m ∧ c.middle.sum = 2*m+s ∧ c.final.sum = 2*m+s+3 ∧
  (∀ x ∈ c.core, x % 2 = 0) ∧ RowsStrip c.core c.middle ∧ RowsStrip c.middle c.final
instance (m s : ℕ) (c : ThreeRowEntry) : Decidable (c.Valid m s) := by
  unfold Valid; infer_instance

lemma support {m s : ℕ} {c : ThreeRowEntry} (h : c.Valid m s)
    (a b : Tableau (ThreeRow.columns m s).sum (columnShape (ThreeRow.columns m s)))
    (t : Tableau (ThreeRow.columns m s).sum (rowDiagram c.final)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, F ≠ 0 := by
  rcases h with ⟨hν,hμ,hc,hm,hf,hev,h1,h2⟩
  let v := canonicalTableau (rowDiagram c.core) (show (rowDiagram c.core).card =
    (ThreeRow.twos m).sum by rw [rowDiagram_card,hc]; simp [ThreeRow.twos,Nat.mul_comm])
  let u := canonicalTableau (rowDiagram c.middle) (show (rowDiagram c.middle).card =
    (ThreeRow.twos m ++ ThreeRow.ones s).sum by
      rw [rowDiagram_card,hm]; simp [ThreeRow.twos,ThreeRow.ones,Nat.mul_comm])
  have heven (i : ℕ) : Even ((rowDiagram c.core).rowLen i) := by
    rw [rowDiagram_rowLen h1.1]
    by_cases hi : i < c.core.length
    · rw [List.getElem?_eq_getElem hi,Option.getD_some]
      exact (Nat.even_iff).mpr (hev _ (List.getElem_mem hi))
    · simp only [List.getElem?_eq_none (Nat.le_of_not_gt hi),Option.getD_none]
      exact ⟨0,rfl⟩
  obtain ⟨F,hF⟩ := ThreeRow.projected_support m s a b v u t heven
    (by rwa [rowDiagram_height h1.1]) (by rwa [rowDiagram_height h2.2.1])
    (rowsStrip_sound h1) (rowsStrip_sound h2)
  refine ⟨F,?_⟩
  intro hz
  exact polytabloid_ne_zero t (congrArg Subtype.val
    (hF (show F ⟨polytabloid t,mem_cyclic _ _⟩ = F 0 by rw [hz]; rfl)))

end ThreeRowEntry

def ThreeRowMask (m s : ℕ) (ps : List ℕ) (cs : List ThreeRowEntry) : Prop :=
  GoodRows ps ∧ ps.length ≤ 3 ∧ ps.sum = 2*m+s+3 ∧
  (∀ c ∈ cs, c.Valid m s) ∧
  ∀ rs ∈ partitionLists 3 (2*m+s+3) (2*m+s+3), RowsDom rs ps →
    rs ∈ cs.map ThreeRowEntry.final
instance (m s : ℕ) (ps : List ℕ) (cs : List ThreeRowEntry) : Decidable (ThreeRowMask m s ps cs) := by
  unfold ThreeRowMask; infer_instance

lemma threeRowMask_support {m s : ℕ} {ps : List ℕ} {cs : List ThreeRowEntry}
    (h : ThreeRowMask m s ps cs)
    (a : Tableau (ThreeRow.columns m s).sum (columnShape (ThreeRow.columns m s)))
    (μ : YoungDiagram) (t : Tableau (ThreeRow.columns m s).sum μ)
    (hd : Dominates μ (rowDiagram ps)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, F ≠ 0 := by
  have hsize : (ThreeRow.columns m s).sum = 2*m+s+3 := by
    simp [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,Nat.mul_comm,Nat.add_assoc]
  have hcard : μ.card = 2*m+s+3 := (tableau_card_eq t).trans hsize
  have ht : μ.card = (rowDiagram ps).card := by rw [hcard,rowDiagram_card,h.2.2.1]
  have hh : μ.colLen 0 ≤ 3 := (height_le_of_dominates ht hd).trans (by
    rw [rowDiagram_height h.1]; exact h.2.1)
  have hm : μ.rowLens ∈ partitionLists 3 (2*m+s+3) (2*m+s+3) := by
    apply mem_partitionLists
    · exact (card_eq_sum_rowLens μ).symm.trans hcard
    · simpa only [YoungDiagram.length_rowLens] using hh
    · exact μ.pos_of_mem_rowLens
    · intro x hx
      rw [← hcard,card_eq_sum_rowLens]
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
    · exact μ.rowLens_sorted
  have hd' : RowsDom μ.rowLens ps := by
    simpa only [rowDiagram_rows h.1] using rowsDom_of_dominates hd
  obtain ⟨c,hc,he⟩ := List.mem_map.mp (h.2.2.2.2 _ hm hd')
  have eqμ : rowDiagram c.final = μ := by rw [he,rowDiagram_rowLens]
  subst μ
  exact ThreeRowEntry.support (h.2.2.2.1 c hc) a a t

end UniversalTensorSquare

namespace Saxl.Balance
open FlagColumns Columns UniversalTensorSquare

theorem WordPacking.threeRows {m s d : ℕ} {ps : List ℕ} {cs : List ThreeRowEntry}
    (hd : 3 ≤ d) (h : ThreeRowMask m s ps cs)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = 1) ↔ output a ∈ Set.Icc 1 3) :
    Nonempty (WordPacking (ThreeRow.columns m s) ps d A label {1}) := by
  have hp : ∀ x ∈ ThreeRow.columns m s, 0 < x := by
    simp only [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,List.mem_append,
      List.mem_replicate,List.mem_singleton]
    intro x hx
    rcases hx with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl <;> omega
  have ht : (rowDiagram ps).card = (ThreeRow.columns m s).sum := by
    rw [rowDiagram_card,h.2.2.1]
    simp [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,Nat.mul_comm,Nat.add_assoc]
  simpa only [rowDiagram_rows h.1] using WordPacking.of_cone_shape
    (columnShape_rows_permutation (ThreeRow.columns m s) hp)
    ((ThreeRow.columns_height m s).trans hd) ht 1 (Set.Icc 1 3) A label he
    (fun a μ t hμ => threeRowMask_support h a μ t hμ)

end Saxl.Balance
end
end

end OAI
