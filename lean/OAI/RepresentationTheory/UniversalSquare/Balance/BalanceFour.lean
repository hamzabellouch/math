import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceDominance
import OAI.RepresentationTheory.UniversalSquare.Specht.CandidateColumns

namespace OAI

/-! Balance Four. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

lemma balanceParts_shape_bounds {M b δ τ ε m : ℕ}
    (hM : 9 ≤ M) (hb : b ≤ M-2) (hδ : δ ≤ 1) (hτ : τ ≤ 1) (hε : ε ≤ 1)
    (heq : M = 4+τ+ε+2*m) (hsmall : τ = 0 → 2*(b+1) ≤ M) :
    let θ := (columnShape (balanceParts M b δ τ ε m)).transpose
    2*M-5 ≤ θ.colLen 0 ∧ θ.rowLen 0 ≤ M+1 ∧ 2 ≤ θ.rowLen 3 := by
  let ps := balanceParts M b δ τ ε m
  let θ := (columnShape ps).transpose
  have hp := balanceParts_positive (M := M) (b := b) (δ := δ) (τ := τ) (ε := ε) (m := m) (by omega)
  have hperm := columnShape_rows_permutation ps hp
  have hlen : ps.length = θ.colLen 0 := by
    simpa only [YoungDiagram.length_rowLens] using hperm.length_eq
  have hlower : 2*M-5 ≤ θ.colLen 0 := hlen ▸ balanceParts_length hδ hτ hε heq
  refine ⟨hlower,?_,?_⟩
  · have hzero : 0 < θ.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    have hh : θ.rowLen 0 ∈ ps := by
      apply hperm.mem_iff.mpr
      rw [← YoungDiagram.get_rowLens (h := hzero)]
      exact List.getElem_mem hzero
    exact balanceParts_bound (by omega) hb hδ hτ hε heq hsmall hh
  · rw [YoungDiagram.rowLen_transpose]
    change 2 ≤ (columnShape ps).colLen 3
    suffices h : 3 < (columnShape ps).rowLen 1 from
      YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    rw [columnShape_rowLen]
    have hfour : List.countP (fun p => decide (1 < p))
        (balancedParts (2*(M-1+b)+1+3*δ) 4) = 4 := by
      rw [List.countP_eq_length.mpr ?_,balancedParts_length]
      intro p hp
      simp only [decide_eq_true_eq]
      have hh := (balancedParts_part hp).1
      omega
    dsimp only [ps,balanceParts,bigParts]
    simp only [List.countP_append,hfour]
    omega

theorem balance_kronecker_pos {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (μ : YoungDiagram) (s : Tableau n μ)
    (hμ : colPrefix μ 4 ≤ 2*M-2) : 0 < kronecker t t s := by
  let τ := if 2*(b+1) ≤ M then 0 else 1
  let ε := (M-4-τ)%2
  let m := (M-4-τ)/2
  have hτ : τ ≤ 1 := by dsimp [τ]; split_ifs <;> omega
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have heq : M = 4+τ+ε+2*m := by dsimp [ε,m]; omega
  have hsmall : τ = 0 → 2*(b+1) ≤ M := by
    intro ht
    by_contra h
    have hh : τ = 1 := ite_eq_right h
    omega
  have hshort : τ ≠ 0 → 1 ≤ b := by
    intro ht
    have hn : ¬ 2*(b+1) ≤ M := by
      intro h
      exact ht (ite_eq_left h)
    omega
  have hheight : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ (by omega)]
    simp [candidateLengths]
  have hpack := balancePacking (by omega) hδ hτ hε heq hshort
  rw [← hheight] at hpack
  obtain ⟨A,label,marks,hordered,⟨P⟩⟩ := hpack
  let rs := balanceColumns M b δ τ ε m
  let ps := balanceParts M b δ τ ε m
  have hperm := balanceColumns_perm (b := b) (δ := δ) (by omega) hτ hε heq
  obtain ⟨e,hr,hc⟩ := place_columns (candidate M b δ) hperm
  have hdegree : rs.sum = n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (((enumerate rs).trans e).trans t.symm)
  subst n
  let a := (enumerate rs).trans e
  have hcand : (candidate M b δ).card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr a).symm
  have htarget : μ.card = rs.sum := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr s).symm
  have hparts : μ.card = (columnShape ps).transpose.card := by
    rw [htarget,transpose_card,columnShape_card]
    exact P.total.symm
  have hn : (staircase M).card ≤ μ.card := by
    rw [htarget,← hcand,candidate_card _ _ _ (by omega)]
    omega
  obtain ⟨hcount,hmax,hfour⟩ := balanceParts_shape_bounds hM hb hδ hτ hε heq hsmall
  have hdom := balance_dominance M hM μ (columnShape ps).transpose hparts hn hμ hcount hmax hfour
  have hpos := P.kronecker_pos a s (standard_placed_self e hr hc)
    (balanceParts_positive (by omega)) hordered hdom
  unfold kronecker spechtRep Specht at hpos ⊢
  rw [spechtSub_tableau_independent a t] at hpos
  exact hpos

theorem balance_kronecker_pos_or_transpose {n M b δ : ℕ} (hM : 9 ≤ M)
    (hb : b ≤ M-2) (hδ : δ ≤ 1) (hn : (candidate M b δ).card = n)
    (μ : YoungDiagram) (hμ : μ.card = n)
    (hsmall : colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  rcases hsmall with h | h
  · exact balance_kronecker_pos hM hb hδ _ μ _ h
  · have hpos := balance_kronecker_pos hM hb hδ (canonicalTableau (candidate M b δ) hn)
      μ.transpose (canonicalTableau μ.transpose ((transpose_card μ).trans hμ)) h
    exact (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr hpos

end UniversalTensorSquare
end
end

end OAI
