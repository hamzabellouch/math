import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.SentinelExhaustion

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def transposeRows (rs : List ℕ) : List ℕ :=
  (List.range (rs.headD 0)).map fun j => rs.countP (fun a => decide (j < a))

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
    transposeRows rs = (rowDiagram rs).transpose.rowLens := by
  conv_lhs => rw [← rowDiagram_rows h,transposeRows_rowLens]

lemma rowDiagram_transposeRows {rs : List ℕ} (h : GoodRows rs) :
    rowDiagram (transposeRows rs) = (rowDiagram rs).transpose := by
  rw [transposeRows_eq h,rowDiagram_rowLens]

def RowsBand (M r : ℕ) (rs : List ℕ) : Prop :=
  ∃ k ∈ List.range 4,
    let d := k+1
    let q := testWidth M d
    d*q+7+d ≤ 2*M-1 ∧ 2*M-1 ≤ (rs.take d).sum ∧
      r ≤ ((List.range q).map fun j => (rs.countP (fun a => decide (j < a))-d)/2).sum
instance (M r : ℕ) (rs : List ℕ) : Decidable (RowsBand M r rs) := by
  unfold RowsBand; infer_instance

lemma rowsBand_sound {M r : ℕ} {rs : List ℕ} (hr : GoodRows rs)
    (h : RowsBand M r rs) : BandTest M r (rowDiagram rs) := by
  obtain ⟨k,hk,hclear,hprefix,hcap⟩ := h
  have hk' : k < 4 := List.mem_range.mp hk
  refine ⟨k+1,by omega,by omega,testWidth M (k+1),min_le_left _ _,?_,hclear,?_⟩
  · rw [rowPrefix_eq_take,rowDiagram_rows hr]
    exact hprefix
  · simpa only [bandCapacity,rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen,
      ← List.sum_toFinset _ List.nodup_range,List.toFinset_range] using hcap

def ResidualProperty (M r : ℕ) (qs : List (List ℕ)) (ls : List (List ℕ))
    (rs : List ℕ) : Prop :=
  RowsBand M r rs ∨ RowsBand M r (transposeRows rs) ∨
    (∃ q ∈ qs, RowsDom rs q ∨ RowsDom (transposeRows rs) q) ∨
    rs ∈ ls ∨ transposeRows rs ∈ ls
instance (M r : ℕ) (qs ls : List (List ℕ)) : DecidablePred (ResidualProperty M r qs ls) := by
  intro rs; unfold ResidualProperty; infer_instance

lemma SquareOccurs.of_packing {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hh : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (hlam : lam.card = n) (hμ : μ.card = n)
    (hd : Dominates μ (rowDiagram p.parts)) : SquareOccurs lam μ := by
  exact ⟨n,canonicalTableau lam hlam,canonicalTableau μ hμ,
    packingPlan_pos p hv hb hh hc hp _ _ hd⟩

lemma residualProperty_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs ls : List (List ℕ)}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (hlists : ∀ rs ∈ ls, SquareOccurs (candidate M b δ) (rowDiagram rs))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : ResidualProperty M r qs ls rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  have hc : (rowDiagram rs).card = n := (rowDiagram_card _).trans hsum
  have ht : (rowDiagram rs).transpose.card = n := (transpose_card _).trans hc
  have hgood' : GoodRows (transposeRows rs) := by
    rw [transposeRows_eq hgood]
    exact ⟨YoungDiagram.rowLens_sorted _,YoungDiagram.pos_of_mem_rowLens _⟩
  have back : SquareOccurs (candidate M b δ) (rowDiagram rs).transpose →
      SquareOccurs (candidate M b δ) (rowDiagram rs) := by
    intro hh
    simpa only [YoungDiagram.transpose_transpose] using hh.target_transpose (candidate_transpose ..)
  rcases h with h | h | ⟨q,hq,h | h⟩ | h | h
  · exact ⟨n,canonicalTableau _ hn,canonicalTableau _ hc,
      band_kronecker_pos hM hδ hre _ _ _ (rowsBand_sound hgood h)⟩
  · have hh := rowsBand_sound hgood' h
    rw [rowDiagram_transposeRows hgood] at hh
    exact back ⟨n,canonicalTableau _ hn,canonicalTableau _ ht,
      band_kronecker_pos hM hδ hre _ _ _ hh⟩
  · exact hcones q hq _ hc (by simpa only [rowDiagram_rows hgood] using h)
  · exact back (hcones q hq _ ht (by simpa only [transposeRows_eq hgood] using h))
  · exact hlists rs h
  · apply back
    simpa only [rowDiagram_transposeRows hgood] using hlists _ h

end UniversalTensorSquare

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma candidate_cone {n M b δ : ℕ} (hM : 4 ≤ M)
    (hn : (candidate M b δ).card = n) (p : PackingPlan) (q : List ℕ)
    (hq : GoodRows q) (hqn : q.sum = n)
    (hv : p.Valid (M+b+δ)) (hb : BandsValid p.bands)
    (hc : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hp : p.parts.Perm q) (μ : YoungDiagram) (hμ : μ.card = n)
    (hd : RowsDom μ.rowLens q) : SquareOccurs (candidate M b δ) μ := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  apply SquareOccurs.of_packing p hv hb hh
  · rw [candidate_transpose,candidate_rowLens hM]; exact hc
  · exact fun a ha => hq.2 a (hp.mem_iff.mp ha)
  · exact hn
  · exact hμ
  · have he : rowDiagram p.parts = rowDiagram q := by
      unfold rowDiagram; rw [columnShape_perm hp]
    rw [he]
    apply dominates_of_rowsDom
    · rw [rowDiagram_card,hqn,hμ]
    · simpa only [rowDiagram_rows hq] using hd

end UniversalTensorSquare
end
end

end OAI
