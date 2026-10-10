import OAI.Topology.CoarseAssembly.SummandComplement
import OAI.Topology.CoarseAssembly.ProjectionBlocks

namespace OAI

/-! # Splitting a block operator into one summand and its complement -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))
variable (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)

theorem blockOperator_single (j : ℕ) (x : H j) :
    CoarseAssembly.blockOperator K C hC hK (summandIsometry H j x) =
      summandIsometry H j (K j x) := by
  apply lp.ext
  funext k
  change K k (lp.single (E := fun k => H k) 2 j x k) =
    lp.single (E := fun k => H k) 2 j (K j x) k
  by_cases hk : j = k
  · subst k
    simp
  · simp [Pi.single_eq_of_ne (Ne.symm hk)]

def complementBlockOperator (j : ℕ) : End (complementHilbertSpace H j) :=
  (complementIsometry H j).toContinuousLinearMap.adjoint.comp
    ((CoarseAssembly.blockOperator K C hC hK).comp
      (complementIsometry H j).toContinuousLinearMap)

theorem complementBlockOperator_coe (j : ℕ) (x : complementHilbertSpace H j) :
    (complementBlockOperator H K C hC hK j x : countableHilbertSpace H) =
      CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H) := by
  unfold complementBlockOperator
  rw [complementIsometry_adjoint]
  change (complementProjection H j
    (CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H)) :
      countableHilbertSpace H) = _
  rw [complementProjection_coe]
  have hx : (x : countableHilbertSpace H) j = 0 := x.property
  change CoarseAssembly.blockOperator K C hC hK (x : countableHilbertSpace H) -
    summandIsometry H j (K j ((x : countableHilbertSpace H) j)) = _
  rw [hx, map_zero, map_zero, sub_zero]

theorem blockOperator_decomposition (j : ℕ) :
    CoarseAssembly.blockOperator K C hC hK =
      operatorConjugation (summandIsometry H j) (K j) +
        operatorConjugation (complementIsometry H j)
          (complementBlockOperator H K C hC hK j) := by
  apply ContinuousLinearMap.ext
  intro x
  unfold operatorConjugation
  rw [summandIsometry_adjoint, complementIsometry_adjoint]
  change CoarseAssembly.blockOperator K C hC hK x =
    summandIsometry H j (K j (x j)) +
      (complementBlockOperator H K C hC hK j (complementProjection H j x) :
        countableHilbertSpace H)
  rw [complementBlockOperator_coe, complementProjection_coe, map_sub, blockOperator_single]
  abel

end CoarseAssembly.Analytic

end

end OAI
