import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.SupportedNormalization

namespace OAI

/-! # Cutting down arbitrary cycles over the unital coefficient algebras

The compact-source algebras used by the circle pairing are unital, although
the Fredholm representations themselves may be nonunital. Restriction to
scalar coefficients gives precisely the local estimates needed for the
represented-subspace cut-down.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem representation_unit_selfAdjoint (c : OddCycle A) :
    IsSelfAdjoint (c.representation 1) := by
  change star (c.representation 1) = c.representation 1
  rw [← map_star, star_one]

theorem representation_unit_sq (c : OddCycle A) :
    c.representation 1 * c.representation 1 = c.representation 1 := by
  rw [← map_mul, one_mul]

theorem representedCutDown_compact (c : OddCycle A) :
    let P := c.representation 1
    let K := symmetricCutDown P c.operator - c.operator
    IsCompactOperator (K * P : End c.space) ∧
      IsCompactOperator (P * K : End c.space) ∧
      IsCompactOperator (star K * P : End c.space) := by
  have h := scalarCutDown_compact c.scalarRestriction
  change let P : End c.space := c.representation (algebraMap ℂ A 1)
         let K : End c.space := symmetricCutDown P c.operator - c.operator
         IsCompactOperator (K * P : End c.space) ∧
           IsCompactOperator (P * K : End c.space) ∧
           IsCompactOperator (star K * P : End c.space) at h
  simpa only [map_one] using h

theorem exists_represented_cutDown (c : OddCycle A) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧ IsSelfAdjoint d.operator ∧
      d.operator * (1 - d.representation 1) = 1 - d.representation 1 := by
  let P := c.representation 1
  let K := symmetricCutDown P c.operator - c.operator
  obtain ⟨hr, hl, hs⟩ := representedCutDown_compact c
  have hp (a : A) : P * c.representation a = c.representation a := by
    change c.representation 1 * c.representation a = c.representation a
    rw [← map_mul, one_mul]
  have hpr (a : A) : c.representation a * P = c.representation a := by
    change c.representation a * c.representation 1 = c.representation a
    rw [← map_mul, mul_one]
  have hr' (a : A) : IsCompactOperator (K * c.representation a : End c.space) := by
    rw [← hp a, ← mul_assoc]
    exact compact_mul_right hr _
  have hl' (a : A) : IsCompactOperator (c.representation a * K : End c.space) := by
    rw [← hpr a, mul_assoc]
    exact compact_mul_left hl _
  have hs' (a : A) : IsCompactOperator (star K * c.representation a : End c.space) := by
    rw [← hp a, ← mul_assoc]
    exact compact_mul_right hs _
  have he : c.operator + K = symmetricCutDown P c.operator := by dsimp only [K]; abel
  refine ⟨c.localCompactPerturb K hr' hl' hs', localCompactPerturb_class c K hr' hl' hs', ?_, ?_⟩
  · change IsSelfAdjoint (c.operator + K)
    rw [he]
    exact symmetricCutDown_selfAdjoint P c.operator (representation_unit_selfAdjoint c)
  · change (c.operator + K) * (1 - P) = 1 - P
    rw [he]
    exact symmetricCutDown_complement P c.operator (representation_unit_selfAdjoint c)
      (representation_unit_sq c)

theorem represented_square_compact (c : OddCycle A)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    IsCompactOperator (c.operator * c.operator - 1 : End c.space) := by
  apply supported_square_compact c.scalarRestriction
  change c.operator * (1 - c.representation (algebraMap ℂ A 1)) =
    1 - c.representation (algebraMap ℂ A 1)
  simpa only [map_one] using hQ

end CoarseAssembly.Analytic

end

end OAI
