import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.PartitionIsometry
import OAI.Topology.CoarseAssembly.BlockOperators

namespace OAI

/-! # The contraction estimate for finite partition localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
@[simp] theorem constantBlock_apply (F : H →L[ℂ] H) (v : Module X H) (x : X) :
    constantBlock F v x = F (v x) := rfl

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_norm_le (F : H →L[ℂ] H) : ‖constantBlock (X := X) F‖ ≤ ‖F‖ :=
  blockOperator_norm_le _ _ _ _

theorem partitionMap_adjoint_apply (a : X → H →L[ℂ] H) (v : Module X H) :
    (partitionMap a).adjoint v = ∑ x, (a x).adjoint (v x) := by
  rw [partitionMap_adjoint]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, coordinate_apply]

theorem partitionCompression_eq_sum (a : X → H →L[ℂ] H) (F : H →L[ℂ] H) :
    partitionCompression a F = ∑ x, (a x).adjoint.comp (F.comp (a x)) := by
  ext v
  simp only [partitionCompression, ContinuousLinearMap.comp_apply, partitionMap_adjoint_apply,
    constantBlock_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  have hx := DFunLike.congr_fun (coordinate_partitionMap a x) v
  exact congrArg (fun h => (a x).adjoint (F h)) hx

theorem partitionCompression_norm_le (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    ‖partitionCompression a F‖ ≤ ‖F‖ := by
  have hv : ‖partitionMap a‖ ≤ 1 := by
    exact (partitionIsometry a hpart).norm_toContinuousLinearMap_le
  have hvs : ‖(partitionMap a).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hv
  calc
    ‖partitionCompression a F‖ ≤ ‖(partitionMap a).adjoint‖ *
        (‖constantBlock (X := X) F‖ * ‖partitionMap a‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖F‖ * 1) := by
      gcongr
      exact constantBlock_norm_le F
    _ = ‖F‖ := by ring

end CoarseAssembly.DiscreteRoe

end

end OAI
