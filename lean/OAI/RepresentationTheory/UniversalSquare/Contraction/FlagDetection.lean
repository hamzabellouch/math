import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking

namespace OAI

/-! Flag Detection. -/

section

noncomputable section
namespace Saxl

lemma cyclic_support_tableau {n d : ℕ} {μ : YoungDiagram}
    (s t : Tableau n μ) (u : WordSpace n d)
    (h : ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 := by
  change ∃ f : Representation.IntertwiningMap (spechtSub s).toRepresentation
    (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 at h
  rw [spechtSub_tableau_independent s t] at h
  exact h

lemma cyclic_support_relabel_iff {n m d : ℕ} {μ : YoungDiagram}
    (e : Fin n ≃ Fin m) (s : Tableau n μ) (t : Tableau m μ) (u : WordSpace n d) :
    (∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep m d) (relabelWord e u)).toRepresentation, f ≠ 0) ↔
    (∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  change (∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (wordRep n d e u)).toRepresentation, f ≠ 0) ↔ _
  rw [cyclic_action_eq]
  constructor
  · exact cyclic_support_tableau t s u
  · exact cyclic_support_tableau s t u

lemma relabelWord_pair {n m d : ℕ} (e : Fin n ≃ Fin m)
    (x y : WordSpace n d) :
    dotProduct (relabelWord e x) (relabelWord e y) = dotProduct x y := by
  classical
  apply Fintype.sum_equiv ((Equiv.arrowCongr e (Equiv.refl _)).symm)
  intro w
  rfl

lemma relabelWord_symm_pair {n m d : ℕ} (e : Fin n ≃ Fin m)
    (x : WordSpace m d) (y : WordSpace n d) :
    dotProduct x (relabelWord e y) = dotProduct (relabelWord e.symm x) y := by
  conv_lhs => rw [← (relabelWord e).apply_symm_apply x]
  exact relabelWord_pair e _ _

lemma relabelWord_alphabet {n m d : ℕ} (e : Fin n ≃ Fin m)
    (P : Fin d → Prop) (u : WordSpace n d) (hu : u ∈ alphabetSub n d P) :
    relabelWord e u ∈ alphabetSub m d P := by
  intro w hw
  obtain ⟨i,hi⟩ := hw
  apply hu
  exact ⟨e.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩

end Saxl
namespace Saxl.FlagColumns
open Columns

lemma blocks_congr_word {d : ℕ} (rs : List ℕ) (N Q : ℕ → Fin d → ℂ)
    (w : Fin rs.sum → Fin d) (h : ∀ i k, N i (w k) = Q i (w k)) :
    blocks rs N w = blocks rs Q w := by
  classical
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pure]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact h _ _

theorem columns_necessary {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (s : Tableau rs.sum μ) (u : WordSpace rs.sum d)
    (P : Fin d → Prop) (hu : u ∈ alphabetSub rs.sum d P)
    (hs : ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep rs.sum d) u).toRepresentation, f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin rs.sum)) (Q : ℕ → Fin d → ℂ),
      (∀ i a, ¬P a → Q i a = 0) ∧
      dotProduct (blocks rs Q) (relabelWord g u) ≠ 0 := by
  classical
  let t := (enumerate rs).trans e
  obtain ⟨f,hf⟩ := cyclic_support_tableau s t u hs
  obtain ⟨g,L,hL⟩ := dual_polytabloid_necessary t u f hf
  rw [(wordMap L).isIntertwining, wordPair_move] at hL
  let N : ℕ → Fin d → ℂ := fun i a => if hi : i < μ.colLen 0 then L ⟨i,hi⟩ a else 0
  have hN : wordMap L (polytabloid t) = blocks rs N := by
    convert (mapped_placed e hr hc N) using 1
    congr 2
    funext i a
    change L i a = if hi : (i : ℕ) < μ.colLen 0 then L ⟨i,hi⟩ a else 0
    simp only [dite_eq_left i.isLt]
  rw [hN] at hL
  let Q : ℕ → Fin d → ℂ := fun i a => if P a then N i a else 0
  refine ⟨g⁻¹,Q,fun i a ha => ite_eq_right ha,?_⟩
  have hu' := relabelWord_alphabet g⁻¹ P u hu
  have he : dotProduct (blocks rs Q) (relabelWord g⁻¹ u) =
      dotProduct (blocks rs N) (relabelWord g⁻¹ u) := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hz : relabelWord g⁻¹ u w = 0
    · simp only [hz,mul_zero]
    · congr 1
      apply blocks_congr_word
      intro i k
      exact ite_eq_left (by
        by_contra hh
        exact hz (hu' w ⟨k,hh⟩))
  rw [he]
  exact hL

theorem columns_sufficient {rs : List ℕ} {μ : YoungDiagram} {d : ℕ}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c c', (e c).val.2 = (e c').val.2 ↔ col c = col c')
    (s : Tableau rs.sum μ) (u : WordSpace rs.sum d) (N : ℕ → Fin d → ℂ)
    (h : dotProduct (blocks rs N) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep rs.sum d) u).toRepresentation, f ≠ 0 := by
  apply cyclic_support_tableau ((enumerate rs).trans e) s u
  apply specht_to_cyclic_of_pair _ (fun i a => N i.val a) u
  rwa [mapped_placed e hr hc N]

end Saxl.FlagColumns
end
end

end OAI
