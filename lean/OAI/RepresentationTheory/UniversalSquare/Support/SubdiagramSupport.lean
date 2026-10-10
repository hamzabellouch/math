import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateSupport

namespace OAI

/-! Subdiagram Support. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def diagonalCut (μ : YoungDiagram) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter (fun c => c.1+c.2 < k)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨μ.isLowerSet hxy hy.1, (Nat.add_le_add hxy.1 hxy.2).trans_lt hy.2⟩

@[simp] lemma mem_diagonalCut (μ : YoungDiagram) (k : ℕ) (c : ℕ × ℕ) :
    c ∈ diagonalCut μ k ↔ c ∈ μ ∧ c.1+c.2 < k := Finset.mem_filter

@[simp] lemma diagonalCut_zero (μ : YoungDiagram) : diagonalCut μ 0 = ⊥ := by
  ext c
  simp

lemma diagonalCut_mono (μ : YoungDiagram) : Monotone (diagonalCut μ) := by
  intro a b hab c hc
  have hc' := (mem_diagonalCut _ _ _).mp hc
  exact (mem_diagonalCut _ _ _).mpr ⟨hc'.1, hc'.2.trans_le hab⟩

lemma diagonalCut_exhausts (μ : YoungDiagram) : ∃ k, diagonalCut μ k = μ := by
  refine ⟨μ.cells.sup (fun c => c.1+c.2+1), ?_⟩
  apply SetLike.ext
  intro c
  simp only [mem_diagonalCut, and_iff_left_iff_imp]
  intro hc
  have h := Finset.le_sup (f := fun c : ℕ × ℕ => c.1+c.2+1) hc
  omega

lemma diagonalCut_strip (ν μ : YoungDiagram) (k : ℕ) :
    HorizontalStrip (ν ⊔ diagonalCut μ k) (ν ⊔ diagonalCut μ (k+1)) := by
  refine ⟨sup_le_sup_left (diagonalCut_mono μ (Nat.le_succ k)) ν, ?_⟩
  intro x hx hnx y hy hny hxy
  have hcut (c : ℕ × ℕ) (hc : c ∈ ν ⊔ diagonalCut μ (k+1))
      (hnc : c ∉ ν ⊔ diagonalCut μ k) : c.1+c.2 = k := by
    simp only [YoungDiagram.mem_sup, mem_diagonalCut] at hc hnc
    rcases hc with hc | hc
    · exact False.elim (hnc (Or.inl hc))
    · have hn : ¬ c.1+c.2 < k := fun hh => hnc (Or.inr ⟨hc.1,hh⟩)
      omega
  have hx' := hcut x hx hnx
  have hy' := hcut y hy hny
  apply Prod.ext <;> omega

theorem subdiagram_stripChain {ν μ : YoungDiagram} (h : ν ≤ μ) :
    ∃ bs : List ℕ, SizedStripChain bs ν μ := by
  have aux (k : ℕ) : ∃ bs : List ℕ, SizedStripChain bs ν (ν ⊔ diagonalCut μ k) := by
    induction k with
    | zero => exact ⟨[], by simpa using SizedStripChain.nil ν⟩
    | succ k ih =>
      obtain ⟨bs,hbs⟩ := ih
      have hs := diagonalCut_strip ν μ k
      have hc := Finset.card_le_card hs.1
      change (ν ⊔ diagonalCut μ k).card ≤ (ν ⊔ diagonalCut μ (k+1)).card at hc
      refine ⟨bs ++ [(ν ⊔ diagonalCut μ (k+1)).card-(ν ⊔ diagonalCut μ k).card], ?_⟩
      exact SizedStripChain.snoc hbs hs (by omega)
  obtain ⟨k,hk⟩ := diagonalCut_exhausts μ
  obtain ⟨bs,hbs⟩ := aux k
  exact ⟨bs, by simpa only [hk, sup_eq_right.mpr h] using hbs⟩

lemma positionProduct_swap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d) :
    positionProduct (e.trans (Equiv.sumComm _ _)) u v = positionProduct e v u := by
  funext w
  change u (rightWord e w) * v (leftWord e w) = _
  exact mul_comm _ _

theorem subdiagram_product_support {n a b d : ℕ} {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (s : Tableau b ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (fv : ∀ (η : YoungDiagram) (r : Tableau a η),
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep a d) v).toRepresentation, F ≠ 0)
    (f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep b d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  obtain ⟨bs,hbs⟩ := subdiagram_stripChain hνμ
  have hv' : v ∈ alphabetSub a d (fun z => ¬¬A z) := by simpa only [not_not] using hv
  have H := strip_product_support hbs s t (e.trans (Equiv.sumComm _ _)) u v
    (fun z => ¬A z) hu hv' f hf (fun η r _ => fv η r)
  rw [positionProduct_swap e v u] at H
  exact H

end Saxl
namespace UniversalTensorSquare
open Saxl

theorem candidate_subdiagram_support {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep r)
      (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (rowColumnCyclic a).toRepresentation,
      F ≠ 0 := by
  have H := subdiagram_product_support hνμ r t (candidateCutPositions a)
    (candidateHighWord M b δ hM) (candidateBandWord hM a)
    (fun α => candidateMark M b ((finProdFinEquiv.symm α).1).val)
    (candidateHighWord_alphabet M b δ hM) (candidateBandWord_alphabet hM a)
    (candidateHighWord_support M b δ hM) f hf
  rw [← candidate_cut_factor hM a] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameMarkProjection _ _ _ (candidateMark M b))
    (rowColumnWord a) F hF

theorem candidate_kronecker_pos_of_subdiagram {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ)) {ν μ : YoungDiagram}
    (hνμ : ν ≤ μ) (r : Tableau (candidateBandSize a) ν) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep r)
      (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation) (hf : f ≠ 0) :
    0 < kronecker a a t := by
  obtain ⟨F,hF⟩ := candidate_subdiagram_support hM a hνμ r t f hf
  exact kronecker_pos_of_rowColumn_support (candidate_transpose M b δ) a a t F hF

end UniversalTensorSquare
end
end

end OAI
