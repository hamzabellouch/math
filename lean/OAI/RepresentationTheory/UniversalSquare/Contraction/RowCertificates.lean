import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.TwoStrip
import OAI.RepresentationTheory.UniversalSquare.Support.SquareSemigroup
import OAI.RepresentationTheory.UniversalSquare.Support.ConstrainedRows

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def rowDiagram (rs : List ℕ) : YoungDiagram := (columnShape rs).transpose

def GoodRows (rs : List ℕ) : Prop := rs.SortedGE ∧ ∀ a ∈ rs, 0 < a
instance (rs : List ℕ) : Decidable (GoodRows rs) := by unfold GoodRows; infer_instance

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma rowDiagram_card (rs : List ℕ) : (rowDiagram rs).card = rs.sum := by
  rw [rowDiagram,transpose_card,columnShape_card]

lemma rowDiagram_rowLen {rs : List ℕ} (h : GoodRows rs) (i : ℕ) :
    (rowDiagram rs).rowLen i = rs[i]?.getD 0 := by
  rw [rowDiagram_eq rs h,ofRowLens_rowLen]

lemma rowDiagram_height {rs : List ℕ} (h : GoodRows rs) :
    (rowDiagram rs).colLen 0 = rs.length := by
  rw [← YoungDiagram.length_rowLens,rowDiagram_rows h]

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

def RowsStrip (rs ss : List ℕ) : Prop :=
  GoodRows rs ∧ GoodRows ss ∧ ∀ i ∈ List.range (max rs.length ss.length),
    rs[i]?.getD 0 ≤ ss[i]?.getD 0 ∧ ss[i+1]?.getD 0 ≤ rs[i]?.getD 0
instance (rs ss : List ℕ) : Decidable (RowsStrip rs ss) := by
  unfold RowsStrip; infer_instance

lemma rowsStrip_sound {rs ss : List ℕ} (h : RowsStrip rs ss) :
    HorizontalStrip (rowDiagram rs) (rowDiagram ss) := by
  have hb (i : ℕ) : (rowDiagram rs).rowLen i ≤ (rowDiagram ss).rowLen i ∧
      (rowDiagram ss).rowLen (i+1) ≤ (rowDiagram rs).rowLen i := by
    rw [rowDiagram_rowLen h.1,rowDiagram_rowLen h.2.1,rowDiagram_rowLen h.2.1]
    by_cases hi : i < max rs.length ss.length
    · exact h.2.2 i (List.mem_range.mpr hi)
    · have hr : rs.length ≤ i := le_trans (le_max_left _ _) (Nat.le_of_not_gt hi)
      have hs : ss.length ≤ i := le_trans (le_max_right _ _) (Nat.le_of_not_gt hi)
      simp [List.getElem?_eq_none hr,List.getElem?_eq_none hs,
        List.getElem?_eq_none (by omega : ss.length ≤ i+1)]
  exact horizontal_of_interlacing _ _ (fun i => (hb i).1) (fun i => (hb i).2)

def RowsChain : List (List ℕ) → List ℕ → List ℕ → List ℕ → Prop
  | [],bs,rs,ss => bs = [] ∧ rs = ss
  | us::cs,bs,rs,ss => ∃ k ∈ List.range (ss.sum+1),
      RowsStrip rs us ∧ rs.sum+k = us.sum ∧ ∃ ks ∈ [bs.drop 1],
        bs = k::ks ∧ RowsChain cs ks us ss

def stripSizes : List ℕ → List (List ℕ) → List ℕ
  | _,[] => []
  | rs,ss::cs => (ss.sum-rs.sum)::stripSizes ss cs

def ChainValid : List ℕ → List (List ℕ) → List ℕ → Prop
  | rs,[],ss => rs=ss
  | rs,us::cs,ss => RowsStrip rs us ∧ rs.sum ≤ us.sum ∧ ChainValid us cs ss
instance (rs : List ℕ) (cs : List (List ℕ)) (ss : List ℕ) : Decidable (ChainValid rs cs ss) := by
  induction cs generalizing rs with
  | nil => unfold ChainValid; infer_instance
  | cons us cs ih =>
    letI := ih us
    unfold ChainValid
    infer_instance

lemma SizedStripChain.trans {bs cs : List ℕ} {ν η μ : YoungDiagram}
    (h : SizedStripChain bs ν η) (h' : SizedStripChain cs η μ) :
    SizedStripChain (bs++cs) ν μ := by
  induction h' with
  | nil => simpa using h
  | snoc hs ht hc ih => simpa [List.append_assoc] using Saxl.SizedStripChain.snoc (ih h) ht hc

lemma chainValid_sound {rs ss : List ℕ} {cs : List (List ℕ)} (h : ChainValid rs cs ss) :
    Saxl.SizedStripChain (stripSizes rs cs) (rowDiagram rs) (rowDiagram ss) := by
  induction cs generalizing rs with
  | nil => have he : rs = ss := h; subst rs; exact Saxl.SizedStripChain.nil _
  | cons us cs ih =>
    have ht : Saxl.SizedStripChain [us.sum-rs.sum] (rowDiagram rs) (rowDiagram us) :=
      Saxl.SizedStripChain.snoc (Saxl.SizedStripChain.nil _) (rowsStrip_sound h.1)
        (by rw [rowDiagram_card,rowDiagram_card]; exact Nat.add_sub_of_le h.2.1)
    exact SizedStripChain.trans ht (ih h.2.2)

def RowsDom (rs ss : List ℕ) : Prop :=
  ∀ k ∈ List.range (ss.length+1), (ss.take k).sum ≤ (rs.take k).sum
instance (rs ss : List ℕ) : Decidable (RowsDom rs ss) := by unfold RowsDom; infer_instance

lemma rowsDom_of_dominates {μ θ : YoungDiagram} (h : Dominates μ θ) :
    RowsDom μ.rowLens θ.rowLens := by
  intro k _
  simpa only [← rowPrefix_eq_take] using h k

lemma dominates_of_rowsDom {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : RowsDom μ.rowLens θ.rowLens) : Dominates μ θ := by
  intro k
  by_cases hk : k ≤ θ.colLen 0
  · rw [rowPrefix_eq_take,rowPrefix_eq_take]
    exact h k (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  · have hh := h (θ.colLen 0) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    rw [← rowPrefix_eq_take,← rowPrefix_eq_take,rowPrefix_eq_card θ le_rfl,← hc] at hh
    rw [rowPrefix_eq_card θ (by omega),← hc]
    exact hh.trans (rowPrefix_mono μ (by omega))

lemma height_le_of_dominates {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : Dominates μ θ) : μ.colLen 0 ≤ θ.colLen 0 := by
  by_contra hn
  have hp : 0 < μ.rowLen (θ.colLen 0) :=
    YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  have hh := h (θ.colLen 0)
  rw [rowPrefix_eq_card θ le_rfl] at hh
  have hk := rowPrefix_le_card μ (θ.colLen 0+1)
  rw [rowPrefix_succ] at hk
  omega

end UniversalTensorSquare
end
end

end OAI
