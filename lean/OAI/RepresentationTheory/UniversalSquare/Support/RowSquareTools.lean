import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.CompactDomainsCore
import OAI.RepresentationTheory.UniversalSquare.Specht.FinitePieri
import OAI.RepresentationTheory.UniversalSquare.Support.NumericalSupport

namespace OAI

/-! Row Square Tools. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

abbrev RowSquare (p q : List ℕ) : Prop := SquareOccurs (rowDiagram p) (rowDiagram q)

lemma columnShape_transposeRows {p : List ℕ} (hp : GoodRows p) :
    columnShape (transposeRows p) = rowDiagram p := by
  rw [transposeRows_eq hp,columnShape_diagram]

lemma rowSquare_transpose {p q : List ℕ} (hp : GoodRows p)
    (h : RowSquare p q) : RowSquare (transposeRows p) q := by
  change SquareOccurs (rowDiagram (transposeRows p)) (rowDiagram q)
  rw [rowDiagram_transposeRows hp]
  exact h.input_transpose

lemma rowSquare_target_transpose {p q : List ℕ} (hp : GoodRows p) (hq : GoodRows q)
    (hs : transposeRows p = p) (h : RowSquare p q) : RowSquare p (transposeRows q) := by
  change SquareOccurs (rowDiagram p) (rowDiagram (transposeRows q))
  rw [rowDiagram_transposeRows hq]
  have ht : (rowDiagram p).transpose = rowDiagram p := by
    rw [← rowDiagram_transposeRows hp,hs]
  exact h.target_transpose ht

def RowJoin (p q x y a b : List ℕ) : Prop :=
  GoodRows p ∧ GoodRows q ∧ GoodRows x ∧ GoodRows y ∧ GoodRows a ∧ GoodRows b ∧
  ((transposeRows x ++ transposeRows y).Perm (transposeRows p) ∨
    (transposeRows x ++ transposeRows y).Perm p) ∧
  ((transposeRows a ++ transposeRows b).Perm (transposeRows q) ∨
    (transposeRows p = p ∧ (transposeRows a ++ transposeRows b).Perm q))
instance (p q x y a b : List ℕ) : Decidable (RowJoin p q x y a b) := by
  unfold RowJoin; infer_instance

lemma rowSquare_join {p q x y a b : List ℕ} (hc : RowJoin p q x y a b)
    (h : RowSquare x a) (h' : RowSquare y b) : RowSquare p q := by
  obtain ⟨hp,hq,hx,hy,ha,hb,hp',hq'⟩ := hc
  unfold RowSquare at h h' ⊢
  rw [← columnShape_transposeRows hx,← columnShape_transposeRows ha] at h
  rw [← columnShape_transposeRows hy,← columnShape_transposeRows hb] at h'
  have hh := h.append h'
  have ht : SquareOccurs (rowDiagram p)
      (columnShape (transposeRows a ++ transposeRows b)) := by
    rcases hp' with hp' | hp'
    · simpa only [columnShape_perm hp',columnShape_transposeRows hp] using hh
    · rw [columnShape_perm hp'] at hh
      exact hh.input_transpose
  rcases hq' with hq' | ⟨hs,hq'⟩
  · simpa only [columnShape_perm hq',columnShape_transposeRows hq] using ht
  · rw [columnShape_perm hq'] at ht
    have hself : (rowDiagram p).transpose = rowDiagram p := by
      rw [← rowDiagram_transposeRows hp,hs]
    exact ht.target_transpose hself

lemma rowSquare_of_cols {p q cs : List ℕ} (hp : GoodRows p) (hq : GoodRows q)
    (he : cs = transposeRows p ∨ cs = p)
    (h : SquareOccurs (columnShape cs) (columnShape (transposeRows q))) : RowSquare p q := by
  rw [columnShape_transposeRows hq] at h
  rcases he with rfl | rfl
  · simpa only [columnShape_transposeRows hp] using h
  · exact h.input_transpose

lemma rowSquare_domain {n : ℕ} {p q cs ts : List ℕ}
    (hp : GoodRows p) (hq : GoodRows q) (hcs : GoodRows cs) (hts : GoodRows ts)
    (he : cs = transposeRows p ∨ cs = p) (ht : ts = transposeRows q)
    (hn : cs.sum = n) (hn' : ts.sum = n)
    (eb : Fin n ≃ Fin cs.sum) (et : Fin n ≃ Fin ts.sum)
    (flag : Finset (ℕ × ℕ × ℕ))
    (hcert : solveDomains n (.full ts) (.full cs) (.full cs)
      (certificateEdges cs cs ts (finCongr hn.symm) eb et) flag ≠ 0) : RowSquare p q := by
  have hc : (columnShape cs).transpose.rowLens = cs := by
    rw [columnShape_sorted cs hcs.1 hcs.2,YoungDiagram.transpose_transpose,
      YoungDiagram.rowLens_ofRowLens_eq_self hcs.2]
  have hd : (columnShape ts).transpose.rowLens = ts := by
    rw [columnShape_sorted ts hts.1 hts.2,YoungDiagram.transpose_transpose,
      YoungDiagram.rowLens_ofRowLens_eq_self hts.2]
  let a := canonicalTableau (columnShape cs) ((columnShape_card _).trans hn)
  let t := canonicalTableau (columnShape ts) ((columnShape_card _).trans hn')
  apply rowSquare_of_cols hp hq he
  rw [← ht]
  refine ⟨n,a,t,kronecker_pos_of_integer_certificate a a t cs cs ts hc hc hd
    (finCongr hn.symm) eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) ?_⟩
  rwa [contractionInteger_solve]

lemma kronecker_pos_of_projected {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ)
    (P : (Fin n → Fin (α.colLen 0 * α.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a P hP).toRepresentation) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨Z,hZ⟩ := subrepresentation_embeds_of_le_range
    ((invariantCoordinateProjection P hP).comp (spechtTensorMap a a))
    (projectedSpechtTensor a a P hP) le_rfl
  exact (kronecker_pos_iff a a t).mpr ⟨Z.comp F,intertwining_comp_ne_zero Z hZ F hF⟩

lemma rowSquare_short {p rs : List ℕ} (q δ : ℕ)
    (hp : GoodRows p) (hr : GoodRows rs) (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2)
    (he : [q+δ,q] = transposeRows p ∨ [q+δ,q] = p)
    (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1),
      rs.countP (fun x => decide (j < x)) % 2 = 1) : RowSquare p rs := by
  have hs : GoodRows [q+δ,q] := by
    constructor
    · apply List.Pairwise.sortedGE; simp
    · simp; omega
  have hc : columnShape [q+δ,q] = (ShortColumns.shape q δ).transpose := by
    rw [columnShape_sorted _ hs.1 hs.2]; rfl
  let a := canonicalTableau (columnShape [q+δ,q])
    (show (columnShape [q+δ,q]).card = 2*q+δ by rw [columnShape_card]; simp; omega)
  let t := canonicalTableau (rowDiagram rs) ((rowDiagram_card _).trans hrs)
  have ha := a
  rw [hc] at ha
  obtain ⟨F,hF⟩ := short_pair_support q δ rfl hδ ha (rowDiagram rs) t
    (by rwa [rowDiagram_height hr]) (by
      intro hd
      obtain ⟨j,_,hj⟩ := ho hd
      exact ⟨j,by simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using hj⟩)
  have hh := kronecker_pos_of_projected ha t _ _ F hF
  apply rowSquare_of_cols hp hr he
  rw [columnShape_transposeRows hr,hc]
  exact ⟨2*q+δ,ha,t,hh⟩

lemma rowSquare_even {p rs : List ℕ} (m : ℕ)
    (hp : GoodRows p) (hr : GoodRows rs) (hm : 0 < m)
    (he : p = [m,m] ∨ transposeRows p = [m,m])
    (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*m) (heven : ∀ r ∈ rs, Even r) :
    RowSquare p rs := by
  let t := canonicalTableau (rowDiagram rs) ((rowDiagram_card _).trans hrs)
  have hev (i : ℕ) : Even ((rowDiagram rs).rowLen i) := by
    rw [rowDiagram_rowLen hr]
    cases h : rs[i]? with
    | none => simp
    | some a => exact heven a (List.mem_of_getElem? h)
  obtain ⟨F,hF⟩ := ShortColumns.even_columnSquare_support m (rowDiagram rs) t hev
    (by rwa [rowDiagram_height hr])
  let a := ShortColumns.evenTableau m
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨Z,hZ⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (columnSquareCyclic a) (polytabloidTensor_cyclic_le_range a a a a)
  have hh : SquareOccurs (ShortColumns.shape m 0) (rowDiagram rs) :=
    ⟨2*m,a,t,(kronecker_pos_iff a a t).mpr
      ⟨Z.comp F,intertwining_comp_ne_zero Z hZ F hF⟩⟩
  have hrows : GoodRows [m,m] := by
    constructor
    · apply List.Pairwise.sortedGE; simp
    · simp; omega
  have hshape : ShortColumns.shape m 0 = rowDiagram [m,m] := by
    rw [rowDiagram_eq _ hrows]; rfl
  rw [hshape] at hh
  rcases he with rfl | he
  · exact hh
  · rw [← he,rowDiagram_transposeRows hp] at hh
    simpa only [YoungDiagram.transpose_transpose] using hh.input_transpose

lemma rowSquare_trivial (p : List ℕ) (hn : 0 < p.sum) : RowSquare p [p.sum] := by
  have hgood : GoodRows [p.sum] := ⟨by apply List.Pairwise.sortedGE; simp,by simpa using hn⟩
  let a := canonicalTableau (rowDiagram p) (rowDiagram_card p)
  let t := canonicalTableau (rowDiagram [p.sum]) (by simpa using rowDiagram_card [p.sum])
  have height : (rowDiagram [p.sum]).colLen 0 = 1 := by rw [rowDiagram_height hgood]; rfl
  let f : Fin ((rowDiagram p).colLen 0) → Fin ((rowDiagram [p.sum]).colLen 0) :=
    fun _ => ⟨0,by omega⟩
  refine ⟨p.sum,a,t,kronecker_pos_of_column_content a t (rowDiagram [p.sum]) rfl
    (fun _ => le_rfl) f ?_⟩
  intro j
  have hj : j.val = 0 := by have := j.isLt; omega
  have heq (i : Fin p.sum) : f (columnLengthWord a i) = j := Fin.ext hj.symm
  simp only [heq,Finset.filter_true,Finset.card_univ,Fintype.card_fin,
    rowDiagram_rowLen hgood,hj]
  rfl

end UniversalTensorSquare
end
end

end OAI
