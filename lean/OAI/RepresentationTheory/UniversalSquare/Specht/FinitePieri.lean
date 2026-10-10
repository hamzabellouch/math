import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.PackingPlans

namespace OAI

/-! Finite Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

def WordPacking.permute {rs ps qs : List ℕ} {d : ℕ}
    {A : Fin (d*d) → Prop} {label : Fin (d*d) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps d A label marks) (h : ps.Perm qs) :
    WordPacking rs qs d A label marks := by
  classical
  let q := Classical.choose (list_get_equiv h)
  have hq := Classical.choose_spec (list_get_equiv h)
  refine {
    word := q ∘ P.word
    counts := ?_
    packing := (P.packing.map (letterLift q)).congr rfl (letterLift_single q P.word)
    marksBound := P.marksBound }
  intro j
  rw [wordContent_lift_equiv,P.counts,← hq,Equiv.apply_symm_apply]

theorem WordPacking.pieri_pos {rs ss ps : List ℕ} {lam L ν μ : YoungDiagram}
    (a : Tableau (rs++ss).sum lam) (s : Tableau rs.sum ν) (t : Tableau (rs++ss).sum μ)
    (e : Cells rs ≃ L.cells) (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (hd : L.colLen 0 ≤ lam.colLen 0)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
    (Q : WordPacking ss ps (lam.colLen 0) A label marks)
    (k : ℕ) (I : Set ℕ) (hk : k ∉ marks)
    (he : ∀ z, (A z ∧ label z = k) ↔ output z ∈ I)
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hv : blocks (rs++ss) (standard (lam.colLen 0)) = polytabloid a)
    (hs : SizedStripChain ps ν μ)
    (F : Representation.IntertwiningMap (spechtRep s)
      (projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
        (inOutputs I) (inOutputs_invariant I)).toRepresentation) (hF : F ≠ 0) :
    0 < kronecker a a t := by
  classical
  let W := projectedSpechtTensor ((enumerate rs).trans e) ((enumerate rs).trans e)
    (inOutputs I) (inOutputs_invariant I)
  let φ := (fiberGroup (fun _ : Fin rs.sum => k)).subtype.comp (singleFiberHom rs.sum k)
  let ψ := (fiberGroup Q.packing.c).subtype.comp Q.packing.φ
  let : AddCommGroup (Representation.coindV φ W.toRepresentation) := Module.addCommMonoidToAddCommGroup ℂ
  let Z := coindLift (ρ := W.toRepresentation) φ (Representation.IntertwiningMap.id W.toRepresentation)
  have hZ : Function.Injective Z := single_coindLift_injective W.toRepresentation k
  let K := Z.comp F
  have hK : K ≠ 0 := intertwining_comp_ne_zero Z hZ F hF
  obtain ⟨T,hT⟩ := stripChain_coind_map hs s t (appendPositions rs ss) φ ψ
    W.toRepresentation Q.packing.τ K hK Q.word Q.counts Q.packing.support
  let P := placedPiece e hr hc hd k I A label he
  have hdis : ∀ (i : Fin rs.sum) (j : Fin ss.sum), k ≠ Q.packing.c j := by
    intro i j hj
    exact hk (hj ▸ Q.marksBound j)
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] Q.packing.Y) := Module.addCommMonoidToAddCommGroup ℂ
  let R := P.join Q.packing.piece (appendPositions rs ss) hdis
  have hh : positionProduct (appendPositions rs ss) (blocks rs (standard (lam.colLen 0)))
      (blocks ss (standard (lam.colLen 0))) = polytabloid a := by
    rw [← blocks_append,hv]
  rw [hh] at R
  exact R.kronecker_pos_of_map a t ho T hT

end Saxl.Balance

namespace Saxl.Balance
open FlagColumns Columns

def pairUpper (q δ : ℕ) : ℕ := if δ = 1 then q+1 else 2*q+3

lemma short_pair_support {n : ℕ} (q δ : ℕ) (hn : n = 2*q+δ)
    (hδ : δ = 1 ∨ δ = 2)
    (a : Tableau n (ShortColumns.shape q δ).transpose)
    (μ : YoungDiagram) (t : Tableau n μ) (hμ : μ.colLen 0 ≤ 4)
    (ho : δ = 2 → ∃ j, μ.colLen j % 2 = 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc q (pairUpper q δ)))
        (inOutputs_invariant (Set.Icc q (pairUpper q δ)))).toRepresentation, F ≠ 0 := by
  subst n
  have hh : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc q (pairUpper q δ)))
        (inOutputs_invariant (Set.Icc q (pairUpper q δ)))).toRepresentation,
      Function.Injective F := by
    rcases hδ with rfl | rfl
    · exact neighboring q a a μ t hμ
    · exact two_paths q a a μ t hμ (ho rfl)
  obtain ⟨F,hF⟩ := hh
  refine ⟨F,?_⟩
  intro hz
  exact polytabloid_ne_zero t (congrArg Subtype.val
    (hF (show F ⟨polytabloid t,mem_cyclic _ _⟩ = F 0 by rw [hz]; rfl)))

end Saxl.Balance

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem pieriPlan_pos {n d q δ : ℕ} (p : PackingPlan) {lam : YoungDiagram}
    {rs ss : List ℕ} {cs : List (List ℕ)}
    (hq : 0 < q) (hδ : δ = 1 ∨ δ = 2) (hp : p.Valid d)
    (hb : BandsValid ((q,pairUpper q δ)::p.bands)) (hk : q ∉ p.marks)
    (hh : lam.colLen 0 = d) (hd : q+δ ≤ d)
    (hc : ([q+δ,q]++p.columns).Perm lam.transpose.rowLens)
    (hr : GoodRows rs) (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*q+δ)
    (ho : δ = 2 → ∃ j ∈ List.range (rs.sum+1), (rs.countP (fun x => decide (j < x))) % 2 = 1)
    (hchain : ChainValid rs cs ss) (hs : p.parts.Perm (stripSizes rs cs))
    (a : Tableau n lam) (t : Tableau n (rowDiagram ss)) : 0 < kronecker a a t := by
  obtain ⟨e,he,he'⟩ := place_columns lam hc
  have hn : ([q+δ,q]++p.columns).sum = n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (((enumerate ([q+δ,q]++p.columns)).trans e).trans a.symm)
  subst n
  have hrows : (ShortColumns.shape q δ).rowLens = [q+δ,q] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)
  obtain ⟨f,hf,hf'⟩ := place_columns (ShortColumns.shape q δ).transpose
    (show [q+δ,q].Perm (ShortColumns.shape q δ).transpose.transpose.rowLens by
      rw [YoungDiagram.transpose_transpose,hrows])
  let s := canonicalTableau (rowDiagram rs)
    (show (rowDiagram rs).card = [q+δ,q].sum by rw [rowDiagram_card,hrs]; simp; omega)
  obtain ⟨F,hF⟩ := short_pair_support q δ (by simp; omega) hδ ((enumerate [q+δ,q]).trans f)
    (rowDiagram rs) s (by rwa [rowDiagram_height hr]) (by
      intro hδ'
      obtain ⟨j,_,hj⟩ := ho hδ'
      exact ⟨j,by simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using hj⟩)
  let B := numericBands ((q,pairUpper q δ)::p.bands) hb
  obtain ⟨Q⟩ := p.realize hp (B.alphabet d) (B.letterLabel d) (by
    intro v hv z
    exact numericBands_iff hb (List.mem_cons_of_mem _ hv) z)
  let Q' := Q.permute hs
  rw [← hh] at Q'
  let a' := (enumerate ([q+δ,q]++p.columns)).trans e
  have ht : 0 < kronecker a' a' t := WordPacking.pieri_pos a' s t f hf hf'
    (by rw [short_transpose_height,hh]; exact hd) Q' q (Set.Icc q (pairUpper q δ)) hk
    (fun z => numericBands_iff hb (List.mem_cons_self ..) z) (B.letter_ordered _)
    (standard_placed_self e he he') (chainValid_sound hchain) F hF
  exact kronecker_pos_of_shapes rfl rfl rfl a' a' t a a t ht

end UniversalTensorSquare
end
end

end OAI
