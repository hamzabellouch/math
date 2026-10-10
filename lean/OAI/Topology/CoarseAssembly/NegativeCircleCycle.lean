import OAI.Topology.CoarseAssembly.EssentialCommutant
import OAI.Topology.CoarseAssembly.ShiftIndex
import OAI.Topology.CoarseAssembly.RawCycleIndex

namespace OAI

/-! # The explicit circle Fredholm cycle and its coordinate index -/

noncomputable section

namespace CoarseAssembly.Analytic

def negativeCircleOperator : End circleSequenceSpace := negativeProjection + negativeProjection - 1

theorem negativeCircleOperator_selfAdjoint : IsSelfAdjoint negativeCircleOperator := by
  change star (negativeProjection + negativeProjection - 1) = _
  rw [star_sub, star_add, negativeProjection_selfAdjoint.star_eq, star_one]
  rfl

theorem negativeCircleOperator_sq : negativeCircleOperator * negativeCircleOperator = 1 := by
  unfold negativeCircleOperator
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, negativeProjection_sq]
  abel

theorem negativeCircleOperator_commutator (f : C(Circle, ℂ)) : IsCompactOperator
    (negativeCircleOperator * circleRepresentation f - circleRepresentation f * negativeCircleOperator) := by
  have he : negativeCircleOperator * circleRepresentation f - circleRepresentation f * negativeCircleOperator =
      (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) +
      (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) := by
    unfold negativeCircleOperator
    noncomm_ring
  rw [he]
  exact (circleRepresentation_commutator f).add (circleRepresentation_commutator f)

def negativeCircleCycle : OddCycle C(Circle, ℂ) where
  space := circleSequenceSpace
  representation := circleRepresentation.toNonUnitalStarAlgHom
  operator := negativeCircleOperator
  commutator_compact := negativeCircleOperator_commutator
  square_compact f := by
    change IsCompactOperator ((negativeCircleOperator * negativeCircleOperator - 1) * circleRepresentation f : End circleSequenceSpace)
    rw [negativeCircleOperator_sq, sub_self, zero_mul]
    exact isCompactOperator_zero
  adjoint_compact f := by
    change IsCompactOperator ((star negativeCircleOperator - negativeCircleOperator) * circleRepresentation f : End circleSequenceSpace)
    rw [negativeCircleOperator_selfAdjoint.star_eq, sub_self, zero_mul]
    exact isCompactOperator_zero

theorem negativeCircleCycle_coordinate_index : rawCycleIndex negativeCircleCycle circleCoordinate = 1 := by
  have hcut : symmetricCutDown (circleRepresentation 1) negativeCircleOperator = negativeCircleOperator := by
    rw [map_one]
    unfold symmetricCutDown
    rw [one_mul, mul_one, negativeCircleOperator_selfAdjoint.star_eq]
    module
  have hpos : positiveProjection negativeCircleOperator = negativeProjection := by
    unfold positiveProjection negativeCircleOperator
    module
  have hunit : circleRepresentation circleCoordinate + (1 - circleRepresentation 1) = bilateralShift := by
    rw [circleRepresentation_coordinate, map_one, sub_self, add_zero]
  unfold rawCycleIndex
  change (toeplitzCompression (positiveProjection
    (symmetricCutDown (circleRepresentation 1) negativeCircleOperator))
    (circleRepresentation circleCoordinate + (1 - circleRepresentation 1))).toLinearMap.index = 1
  rw [hcut, hpos, hunit]
  exact shiftToeplitz_index

end CoarseAssembly.Analytic

end

end OAI
