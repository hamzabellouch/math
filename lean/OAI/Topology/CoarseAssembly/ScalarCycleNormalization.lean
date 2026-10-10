import OAI.Topology.CoarseAssembly.InvolutiveNormalization

namespace OAI

/-! # Vanishing of unital scalar Fredholm cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem scalar_representation (c : OddCycle ℂ) (z : ℂ) :
    c.representation z = z • c.representation 1 := by
  simpa using c.representation.map_smul z (1 : ℂ)

theorem scalar_involutive_degenerate (c : OddCycle ℂ)
    (hunit : c.representation 1 = 1) (hself : IsSelfAdjoint c.operator)
    (hsq : c.operator * c.operator = 1) : c.Degenerate := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [scalar_representation, hunit, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
  · intro z
    rw [hsq, sub_self, zero_mul]
  · intro z
    rw [hself.star_eq, sub_self, zero_mul]

theorem unital_scalar_cycleClass_zero (c : OddCycle ℂ) (hunit : c.representation 1 = 1) :
    cycleClass ℂ c = 0 := by
  obtain ⟨d, hdc, hdu, hds, hsq⟩ := exists_involutive_representative c hunit
  exact hdc.symm.trans (degenerate_zero d (scalar_involutive_degenerate d hdu hds hsq))

end CoarseAssembly.Analytic

end

end OAI
