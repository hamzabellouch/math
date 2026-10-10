import OAI.Topology.CoarseAssembly.CircleSequenceRepresentation
import OAI.Topology.CoarseAssembly.ToeplitzProductIndex
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

namespace OAI

/-! # Extending compact commutators from the circle coordinate to every function -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

variable {H : HilbertSpace}

theorem compact_commutator_add (P T S : End H)
    (hT : IsCompactOperator (P * T - T * P : End H))
    (hS : IsCompactOperator (P * S - S * P : End H)) :
    IsCompactOperator (P * (T + S) - (T + S) * P : End H) := by
  have he : P * (T + S) - (T + S) * P = (P * T - T * P) + (P * S - S * P) := by noncomm_ring
  rw [he]
  exact hT.add hS

/-- Operators commuting with `P` modulo compacts, together with their adjoints. -/
def compactCommutant (P : End H) : StarSubalgebra ℂ (End H) where
  carrier := {T | IsCompactOperator (P * T - T * P : End H) ∧
    IsCompactOperator (P * star T - star T * P : End H)}
  zero_mem' := by
    change IsCompactOperator (P * 0 - 0 * P : End H) ∧ IsCompactOperator (P * star 0 - star 0 * P : End H)
    simp only [star_zero, mul_zero, zero_mul, sub_self]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  one_mem' := by
    change IsCompactOperator (P * 1 - 1 * P : End H) ∧ IsCompactOperator (P * star 1 - star 1 * P : End H)
    simp only [star_one, mul_one, one_mul, sub_self]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  add_mem' hT hS := by
    refine ⟨compact_commutator_add P _ _ hT.1 hS.1, ?_⟩
    rw [star_add]
    exact compact_commutator_add P _ _ hT.2 hS.2
  mul_mem' hT hS := by
    refine ⟨compact_commutator_mul P _ _ hT.1 hS.1, ?_⟩
    rw [star_mul]
    exact compact_commutator_mul P _ _ hS.2 hT.2
  algebraMap_mem' z := by
    have hz (z : ℂ) : P * algebraMap ℂ (End H) z - algebraMap ℂ (End H) z * P = 0 :=
      sub_eq_zero.mpr (Algebra.commutes z P).symm
    change IsCompactOperator (P * algebraMap ℂ (End H) z - algebraMap ℂ (End H) z * P) ∧
      IsCompactOperator (P * star (algebraMap ℂ (End H) z) - star (algebraMap ℂ (End H) z) * P)
    have hs : star (algebraMap ℂ (End H) z) = algebraMap ℂ (End H) (star z) := by
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
    rw [hz, hs, hz]
    exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  star_mem' {T} hT := by
    change IsCompactOperator (P * star T - star T * P) ∧
      IsCompactOperator (P * star (star T) - star (star T) * P)
    exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactCommutant_closed (P : End H) : IsClosed (compactCommutant P : Set (End H)) := by
  change IsClosed ({T : End H | IsCompactOperator (P * T - T * P)} ∩
    {T : End H | IsCompactOperator (P * star T - star T * P)})
  exact (isClosed_setOfPred_isCompactOperator.preimage
    ((continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const))).inter
      (isClosed_setOfPred_isCompactOperator.preimage
        ((continuous_const.mul continuous_star).sub (continuous_star.mul continuous_const)))

theorem circleRepresentation_commutator (f : C(Circle, ℂ)) : IsCompactOperator
    (negativeProjection * circleRepresentation f - circleRepresentation f * negativeProjection) := by
  let S : StarSubalgebra ℂ C(Circle, ℂ) :=
    (compactCommutant negativeProjection).comap circleRepresentation
  have hcoord : circleCoordinate ∈ S := by
    change IsCompactOperator (negativeProjection * circleRepresentation circleCoordinate -
      circleRepresentation circleCoordinate * negativeProjection) ∧
      IsCompactOperator (negativeProjection * star (circleRepresentation circleCoordinate) -
      star (circleRepresentation circleCoordinate) * negativeProjection)
    rw [circleRepresentation_coordinate]
    exact ⟨negativeProjection_commutator_compact,
      compact_commutator_star_unitary _ _ bilateralShift_unitary.1 bilateralShift_unitary.2
        negativeProjection_commutator_compact⟩
  have hsep : S.SeparatesPoints := by
    intro x y hxy
    exact ⟨circleCoordinate, ⟨circleCoordinate, hcoord, rfl⟩, fun he => hxy (Circle.coe_injective he)⟩
  have htop : S.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  have hclosed : IsClosed (S : Set C(Circle, ℂ)) :=
    (compactCommutant_closed negativeProjection).preimage (map_continuous circleRepresentation)
  have hle : S.topologicalClosure ≤ S := StarSubalgebra.topologicalClosure_minimal le_rfl hclosed
  rw [htop] at hle
  have hf : f ∈ S := hle (by trivial)
  exact hf.1

end CoarseAssembly.Analytic

end

end OAI
