import OAI.Topology.CoarseAssembly.FredholmInvertible

namespace OAI

/-! # Invertible self-adjoint representatives for unital odd cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem exists_invertible_selfAdjoint_representative (c : OddCycle A)
    (hunital : c.representation 1 = 1) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧
      d.representation 1 = 1 ∧ IsSelfAdjoint d.operator ∧ IsUnit d.operator := by
  obtain ⟨d, hdc, hdunit, hdself⟩ := exists_selfAdjoint_representative c hunital
  have hc : IsCompactOperator (d.operator * d.operator - 1 : End d.space) := by
    simpa only [hdunit, mul_one] using d.square_compact 1
  have hp := kernelProjection_compact d.operator hc
  have hps : IsCompactOperator (star (kernelProjection d.operator) : End d.space) := by
    rw [(kernelProjection_selfAdjoint d.operator).star_eq]
    exact hp
  refine ⟨d.compactPerturb (kernelProjection d.operator) hp hps,
    (compactPerturb_class d _ hp hps).trans hdc, hdunit,
    kernel_corrected_selfAdjoint d.operator hdself, kernel_corrected_isUnit d.operator hdself hc⟩

end CoarseAssembly.Analytic

end

end OAI
