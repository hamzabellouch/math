import OAI.Topology.CoarseAssembly.HilbertHeadTail
import OAI.Topology.CoarseAssembly.FiniteCycleSum

namespace OAI

/-! # Splitting the first summand off a finite active cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem blockOperator_head_tail (H : ℕ → HilbertSpace) (T : ∀ j, End (H j))
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ j, ‖T j‖ ≤ C) :
    blockOperator T C hC hT =
      operatorConjugation (summandIsometry H 0) (T 0) +
        operatorConjugation (tailInsert H)
          (blockOperator (fun j => T (j + 1)) C hC (fun j => hT (j + 1))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  have hh : (summandIsometry H 0).toContinuousLinearMap.adjoint x = x 0 := by
    rw [summandIsometry_adjoint]
    rfl
  change T j (x j) =
    (lp.single (E := fun j => H j) 2 0 (T 0 ((summandIsometry H 0).toContinuousLinearMap.adjoint x))) j +
      (tailInsert H ((blockOperator (fun j => T (j + 1)) C hC (fun j => hT (j + 1)))
        ((tailInsert H).toContinuousLinearMap.adjoint x))) j
  rw [hh]
  cases j with
  | zero => rw [tailInsert_zero]; simp
  | succ j =>
    rw [tailInsert_succ, blockOperator_apply, tailInsert_adjoint_apply]
    simp

variable {A : Type} [CStarAlgebra A]

def finiteActiveCycle_head_tail (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N + 1 ≤ j → (c j).Degenerate) :
    (c 0).IsDirectSum
      (finiteActiveCycle (fun j => c (j + 1)) C hC (fun j => hF (j + 1)) N
        (fun j hj => htail (j + 1) (Nat.add_le_add_right hj 1)))
      (finiteActiveCycle c C hC hF (N + 1) htail) where
  left := summandIsometry (familyHilbert c) 0
  right := tailInsert (familyHilbert c)
  orthogonal := head_tail_orthogonal _
  exhaustive := head_tail_exhaustive _
  representation_eq a := blockOperator_head_tail (familyHilbert c)
    (fun j => (c j).representation a) ‖a‖ (norm_nonneg a)
    (fun _ => NonUnitalStarAlgHom.norm_apply_le _ _)
  operator_eq := blockOperator_head_tail (familyHilbert c) (fun j => (c j).operator) C hC hF

end CoarseAssembly.Analytic

end

end OAI
