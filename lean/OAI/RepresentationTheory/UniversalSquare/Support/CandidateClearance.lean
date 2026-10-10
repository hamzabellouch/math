import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateCut
import OAI.RepresentationTheory.UniversalSquare.Band.PathGeometry

namespace OAI

/-! Candidate Clearance. -/

section

noncomputable section
namespace Saxl

lemma altWord_support {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a w : Fin n → Fin d) (hw : altWord G a w ≠ 0) :
    ∃ g : G, w = a ∘ g.val := by
  classical
  let := Fintype.ofFinite G
  rw [altWord_inverse_sum] at hw
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw
  obtain ⟨g, hg, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine ⟨g, ?_⟩
  by_contra he
  exact hn (by rw [Pi.single_eq_of_ne he, mul_zero])

end Saxl

namespace UniversalTensorSquare
open Saxl

lemma candidateRotateRow_small {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hr : 2 ≤ x.val.1)
    (ht : M-2 ≤ x.val.1+x.val.2) :
    (candidateRotateRow M b δ hM x).val.2 < 2 := by
  have hx := mem_candidate.mp x.property
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) < 2
  rw [ite_eq_right (by omega)]
  rcases x with ⟨⟨i,j⟩,hx0⟩
  dsimp only at *
  split_ifs <;> omega

lemma candidateRotateCol_small {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hc : 2 ≤ x.val.2)
    (ht : M-2 ≤ x.val.1+x.val.2) :
    (candidateRotateCol M b δ hM x).val.1 < 2 := by
  apply candidateRotateRow_small hM (candidateSwap M b δ x) hc
  change M-2 ≤ x.val.2+x.val.1
  omega

lemma candidateBandTableau_outside {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (i : Fin (candidateBandSize t)) :
    M-2 ≤ (candidateBandTableau t i).val.1 + (candidateBandTableau t i).val.2 := by
  have hh := candidateCutPositions_high t ((candidateCutPositions t).symm (Sum.inr i))
  rw [Equiv.apply_symm_apply] at hh
  have hn : ¬candidateTriangle t ((candidateCutPositions t).symm (Sum.inr i)) := by
    intro h
    have he := hh.mpr h
    exact Bool.false_ne_true he
  exact Nat.le_of_not_gt hn

lemma candidateBandRow_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateRow M b δ hM (candidateBandTableau t i)).val.2 := by
  simp only [rightWord, Function.comp_apply, rowWord, transposeTableau,
    candidateRotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

lemma candidateBandCol_seed {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) (i : Fin (candidateBandSize t)) :
    (rightWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))) i).val =
        (candidateRotateCol M b δ hM (candidateBandTableau t i)).val.1 := by
  simp only [rightWord, Function.comp_apply, rowWord,
    candidateRotateColPositions, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem candidateBandRow_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) → Fin ((candidate M b δ).transpose.colLen 0))
    (hw : candidateBandRow hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.1) : (w i).val < 2 := by
  obtain ⟨g,rfl⟩ := altWord_support _ _ w hw
  have hg := g.property i
  change (candidateBandTableau t (g.val i)).val.1 = (candidateBandTableau t i).val.1 at hg
  change (rightWord (candidateCutPositions t) _ (g.val i)).val < 2
  rw [candidateBandRow_seed]
  exact candidateRotateRow_small hM _ (by rwa [hg]) (candidateBandTableau_outside t _)

theorem candidateBandCol_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) → Fin ((candidate M b δ).colLen 0))
    (hw : candidateBandCol hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.2) : (w i).val < 2 := by
  obtain ⟨g,rfl⟩ := altWord_support _ _ w hw
  have hg := g.property i
  change (candidateBandTableau t (g.val i)).val.2 = (candidateBandTableau t i).val.2 at hg
  change (rightWord (candidateCutPositions t) _ (g.val i)).val < 2
  rw [candidateBandCol_seed]
  exact candidateRotateCol_small hM _ (by rwa [hg]) (candidateBandTableau_outside t _)

def candidatePathAlphabet (M b δ : ℕ) :
    Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → Prop :=
  fun a => ((finProdFinEquiv.symm a).1).val < 2 ∧ ((finProdFinEquiv.symm a).2).val < 2

theorem candidateBandWord_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (hi : 2 ≤ (candidateBandTableau t i).val.1)
    (hj : 2 ≤ (candidateBandTableau t i).val.2) :
    candidatePathAlphabet M b δ (w i) := by
  rw [candidateBandWord, wordTensor_tmul] at hw
  exact ⟨candidateBandRow_clearance hM t _ (mul_ne_zero_iff.mp hw).1 i hi,
    candidateBandCol_clearance hM t _ (mul_ne_zero_iff.mp hw).2 i hj⟩

theorem candidateBandWord_path_clearance {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ))
    (w : Fin (candidateBandSize t) →
      Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0))
    (hw : candidateBandWord hM t w ≠ 0) (i : Fin (candidateBandSize t))
    (q : Fin (2*M-1)) (hq : (candidateBandTableau t i).val = candidatePathCell M b δ q)
    (hle : 4 ≤ q.val) (hri : q.val+4 < 2*M-1) : candidatePathAlphabet M b δ (w i) := by
  obtain ⟨ha,hb⟩ := path_endpoint_clearance M b δ hM q hle hri
  apply candidateBandWord_clearance hM t w hw i <;> rwa [hq]

end UniversalTensorSquare
end
end

end OAI
