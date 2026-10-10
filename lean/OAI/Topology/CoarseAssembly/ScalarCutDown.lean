import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ScalarCycleNormalization
import OAI.Topology.CoarseAssembly.LocalCompactPerturbation

namespace OAI

/-! # Cutting a scalar Fredholm operator down to its represented subspace -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem symmetricCutDown_selfAdjoint (P F : End H) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (symmetricCutDown P F) := by
  change star ((1 / 2 : ℝ) • (P * F * P + star (P * F * P)) + (1 - P)) = _
  rw [star_add, star_smul, star_trivial, star_add, star_star, star_sub, star_one, hP.star_eq]
  rw [add_comm (star (P * F * P))]
  rfl

theorem symmetricCutDown_complement (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) : symmetricCutDown P F * (1 - P) = 1 - P := by
  have hzero : ∀ T : End H, P * T * P * (1 - P) = 0 := by
    intro T
    rw [mul_sub, mul_one, mul_assoc (P * T) P P, hPP, sub_self]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  unfold symmetricCutDown
  rw [add_mul, smul_mul_assoc, add_mul, hzero F,
    star_mul, star_mul, hP.star_eq, ← mul_assoc, hzero (star F), add_zero, smul_zero, zero_add, hQ]

theorem scalar_projection_selfAdjoint (c : OddCycle ℂ) : IsSelfAdjoint (c.representation 1) := by
  change star (c.representation 1) = c.representation 1
  rw [← map_star, star_one]

theorem scalar_projection_sq (c : OddCycle ℂ) : c.representation 1 * c.representation 1 =
    c.representation 1 := by rw [← map_mul, one_mul]

theorem symmetricCutDown_sub_mul (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) :
    (symmetricCutDown P F - F) * P = -(F * P - P * F) * P +
      (1 / 2 : ℝ) • (P * ((star F - F) * P)) := by
  simp only [symmetricCutDown, sub_mul, add_mul, smul_mul_assoc,
    star_mul, hP.star_eq, mul_sub, mul_assoc, hPP, one_mul, neg_mul]
  module

theorem mul_symmetricCutDown_sub (P F : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) :
    P * (symmetricCutDown P F - F) = P * (F * P - P * F) +
      (1 / 2 : ℝ) • (P * ((star F - F) * P)) := by
  simp only [symmetricCutDown, mul_sub, mul_add, mul_smul_comm,
    star_mul, hP.star_eq, sub_mul, ← mul_assoc, hPP, mul_one]
  module

theorem scalarCutDown_compact (c : OddCycle ℂ) :
    let P := c.representation 1
    let K := symmetricCutDown P c.operator - c.operator
    IsCompactOperator (K * P : End c.space) ∧
      IsCompactOperator (P * K : End c.space) ∧
      IsCompactOperator (star K * P : End c.space) := by
  let P := c.representation 1
  let K := symmetricCutDown P c.operator - c.operator
  have hp : IsSelfAdjoint P := scalar_projection_selfAdjoint c
  have hpp : P * P = P := scalar_projection_sq c
  have hd := c.adjoint_compact 1
  have hc := c.commutator_compact 1
  have hr : IsCompactOperator (K * P : End c.space) := by
    dsimp only [K]
    rw [symmetricCutDown_sub_mul P c.operator hp hpp]
    exact (compact_mul_right hc.neg P).add ((compact_mul_left hd P).smul (1 / 2 : ℝ))
  have hl : IsCompactOperator (P * K : End c.space) := by
    dsimp only [K]
    rw [mul_symmetricCutDown_sub P c.operator hp hpp]
    exact (compact_mul_left hc P).add ((compact_mul_left hd P).smul (1 / 2 : ℝ))
  refine ⟨hr, hl, ?_⟩
  have he : star K * P = K * P - (star c.operator - c.operator) * P := by
    dsimp only [K]
    rw [star_sub, (symmetricCutDown_selfAdjoint P c.operator hp).star_eq]
    noncomm_ring
  rw [he]
  exact hr.sub hd

theorem exists_supported_scalar_representative (c : OddCycle ℂ) :
    ∃ d : OddCycle ℂ, cycleClass ℂ d = cycleClass ℂ c ∧ IsSelfAdjoint d.operator ∧
      d.operator * (1 - d.representation 1) = 1 - d.representation 1 := by
  let P := c.representation 1
  let K := symmetricCutDown P c.operator - c.operator
  obtain ⟨hr, hl, hs⟩ := scalarCutDown_compact c
  have hr' (z : ℂ) : IsCompactOperator (K * c.representation z : End c.space) := by
    rw [scalar_representation, mul_smul_comm]
    exact hr.smul z
  have hl' (z : ℂ) : IsCompactOperator (c.representation z * K : End c.space) := by
    rw [scalar_representation, smul_mul_assoc]
    exact hl.smul z
  have hs' (z : ℂ) : IsCompactOperator (star K * c.representation z : End c.space) := by
    rw [scalar_representation, mul_smul_comm]
    exact hs.smul z
  have he : c.operator + K = symmetricCutDown P c.operator := by dsimp only [K]; abel
  refine ⟨c.localCompactPerturb K hr' hl' hs', localCompactPerturb_class c K hr' hl' hs', ?_, ?_⟩
  · change IsSelfAdjoint (c.operator + K)
    rw [he]
    exact symmetricCutDown_selfAdjoint P c.operator (scalar_projection_selfAdjoint c)
  · change (c.operator + K) * (1 - P) = 1 - P
    rw [he]
    exact symmetricCutDown_complement P c.operator (scalar_projection_selfAdjoint c)
      (scalar_projection_sq c)

theorem supported_square_compact (c : OddCycle ℂ)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    IsCompactOperator (c.operator * c.operator - 1 : End c.space) := by
  have hz : (c.operator * c.operator - 1) * (1 - c.representation 1) = 0 := by
    calc
      _ = c.operator * (c.operator * (1 - c.representation 1)) -
          (1 - c.representation 1) := by noncomm_ring
      _ = 0 := by rw [hQ, hQ, sub_self]
  have he : c.operator * c.operator - 1 =
      (c.operator * c.operator - 1) * c.representation 1 := by
    exact sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hz)
  rw [he]
  exact c.square_compact 1

end CoarseAssembly.Analytic

end

end OAI
