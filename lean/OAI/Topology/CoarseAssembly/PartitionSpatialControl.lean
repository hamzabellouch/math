import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.PartitionCompression

namespace OAI

/-! # Spatial control of the partition-localized operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partitionMap_adjoint_insert (a : X → H →L[ℂ] H) (y : X) :
    (partitionMap a).adjoint.comp (insert y) = (a y).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (coordinate_partitionMap a y)
  simpa only [ContinuousLinearMap.adjoint_comp, coordinate_adjoint] using h

theorem entry_partitionConjugate (a : X → H →L[ℂ] H) (F : H →L[ℂ] H) (x y : X) :
    entry (partitionConjugate a F) x y = a x * F * (a y).adjoint := by
  calc
    entry (partitionConjugate a F) x y =
        ((coordinate x).comp (partitionMap a)).comp
          (F.comp ((partitionMap a).adjoint.comp (insert y))) := by
      simp only [entry, partitionConjugate, ContinuousLinearMap.comp_assoc]
    _ = _ := by
      rw [coordinate_partitionMap, partitionMap_adjoint_insert]
      rfl

variable [PseudoMetricSpace X]

theorem partitionConjugate_one_propagation (a : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) :
    PropagationLE r (partitionConjugate a 1) := by
  intro x y hxy
  rw [entry_partitionConjugate, ha y, mul_one]
  exact hsupport x y hxy

theorem partitionLocalization_propagation (a : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) (F : H →L[ℂ] H) :
    PropagationLE (r + r) (partitionConjugate a (partitionCompression a F)) := by
  intro x y hxy
  rw [entry_partitionConjugate, partitionCompression_eq_sum, ha y]
  change a x * (∑ z, (a z).adjoint * F * a z) * a y = 0
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro z _
  rw [ha z]
  by_cases hxz : r < dist x z
  · rw [← mul_assoc (a x), ← mul_assoc (a x), hsupport x z hxz, zero_mul, zero_mul,
      zero_mul]
  · have hzy : r < dist z y := by
      have ht := dist_triangle x z y
      have hxz' := le_of_not_gt hxz
      linarith
    simp only [mul_assoc, hsupport z y hzy, mul_zero]

end CoarseAssembly.DiscreteRoe

end

end OAI
