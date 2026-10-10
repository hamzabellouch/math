import OAI.Topology.CoarseAssembly.PartitionIsometry

namespace OAI

/-! # A finite-coordinate estimate for partition isometries -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [Fintype X] in
theorem insert_norm_le_one (x : X) : ‖insert (H := H) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖lp.single (E := fun _ : X => H) 2 x v‖ ≤ 1 * ‖v‖
  simpa only [one_mul] using
    (lp.norm_single (E := fun _ : X => H) (by norm_num : (0 : ENNReal) < 2) x v).le

theorem partitionMap_sub (a b : X → H →L[ℂ] H) :
    partitionMap a - partitionMap b = ∑ x, (insert x).comp (a x - b x) := by
  simp only [partitionMap, ContinuousLinearMap.comp_sub, Finset.sum_sub_distrib]

theorem partitionMap_sub_norm_le_sum (a b : X → H →L[ℂ] H) :
    ‖partitionMap a - partitionMap b‖ ≤ ∑ x, ‖a x - b x‖ := by
  rw [partitionMap_sub]
  apply (norm_sum_le Finset.univ (fun x => (insert (H := H) x).comp (a x - b x))).trans
  apply Finset.sum_le_sum
  intro x _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (insert_norm_le_one (H := H) x) (norm_nonneg (a x - b x)))

end CoarseAssembly.DiscreteRoe

end

end OAI
