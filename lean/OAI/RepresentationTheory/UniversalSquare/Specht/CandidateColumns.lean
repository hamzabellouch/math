import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceAssembly

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]
    simp [candidateLengths]
  apply List.ext_getElem
  · simp only [YoungDiagram.length_rowLens,hh,List.length_append,List.length_cons,
      List.length_nil,List.length_reverse,List.length_range',List.length_replicate]
    omega
  · intro i hi hj
    rw [YoungDiagram.get_rowLens,candidate_rowLen _ _ _ _ hM]
    by_cases hi0 : i = 0
    · subst i
      simp [candidateLengths]
    by_cases hi1 : i = 1
    · subst i
      simp [candidateLengths]
    have hi2 : 2 ≤ i := by omega
    have hlen : i < M+b+δ := by simpa only [YoungDiagram.length_rowLens,hh] using hi
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons,List.length_nil, Nat.zero_add]
    simp only [candidateLengths,ite_eq_right hi0,ite_eq_right hi1]
    by_cases him : i < M-2
    · rw [ite_eq_left him,List.getElem_append_left (by simp; omega),List.getElem_reverse,
        List.getElem_range']
      simp only [List.length_range',Nat.one_mul]
      omega
    · rw [ite_eq_right him,List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse,List.length_range']
      by_cases hib : i < M-1+b
      · rw [ite_eq_left hib,List.getElem_append_left (by simp; omega),List.getElem_replicate]
      · rw [ite_eq_right hib,ite_eq_left hlen,List.getElem_append_right (by simp; omega),
          List.getElem_replicate]

lemma oneIf_range {x ε : ℕ} (hε : ε ≤ 1) : oneIf x ε = List.range' x ε := by
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl <;> simp [oneIf,List.range']

lemma balanceColumns_perm {M b δ τ ε m : ℕ}
    (hM : 4 ≤ M) (hτ : τ ≤ 1) (hε : ε ≤ 1) (heq : M = 4+τ+ε+2*m) :
    (balanceColumns M b δ τ ε m).Perm (candidate M b δ).transpose.rowLens := by
  rw [candidate_transpose,candidate_rowLens (by omega)]
  have hrun : oneIf 3 τ ++ oneIf (3+τ) ε ++ List.range' (3+τ+ε) (2*m) =
      List.range' 3 (M-4) := by
    rw [oneIf_range hτ,oneIf_range hε,List.range'_append_1, Nat.add_assoc 3 τ ε,List.range'_append_1]
    congr 1
    omega
  apply List.perm_iff_count.mpr
  intro x
  simp only [balanceColumns,bigColumns,shortColumns,List.count_append,List.count_reverse,
    (pairColumns_perm (3+τ+ε) m).count_eq,show M-1+b+1+δ = M+b+δ by omega]
  have hh := congrArg (List.count x) hrun
  simp only [List.count_append] at hh
  omega

end UniversalTensorSquare
end
end

end OAI
