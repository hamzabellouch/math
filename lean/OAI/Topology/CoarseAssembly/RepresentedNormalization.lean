import OAI.Topology.CoarseAssembly.RepresentedCutDown

namespace OAI

/-! # Involutive representatives with possibly nonunital representations -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem exists_supported_involution (c : OddCycle A) (hF : IsSelfAdjoint c.operator)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    ∃ e : OddCycle A, cycleClass A e = cycleClass A c ∧ IsSelfAdjoint e.operator ∧
      e.operator * e.operator = 1 ∧ Commute e.operator (e.representation 1) := by
  let P : End c.space := c.representation 1
  have hc := represented_square_compact c hQ
  have hk := kernelProjection_compact c.operator hc
  have hks : IsCompactOperator (star (kernelProjection c.operator) : End c.space) := by
    rw [(kernelProjection_selfAdjoint c.operator).star_eq]
    exact hk
  let G : End c.space := c.operator + kernelProjection c.operator
  have hgs : IsSelfAdjoint G := kernel_corrected_selfAdjoint c.operator hF
  have hgi : IsUnit G := kernel_corrected_isUnit c.operator hF hc
  have hgQ : G * (1 - P) = 1 - P := by
    change (c.operator + kernelProjection c.operator) * (1 - P) = 1 - P
    rw [add_mul, kernelProjection_complement c.operator P hF hQ, add_zero]
    exact hQ
  have hgcomm : Commute G P :=
    commute_of_complement G P hgs (representation_unit_selfAdjoint c) hgQ
  have hgcpt : IsCompactOperator (G * G - 1 : End c.space) :=
    kernel_corrected_compact_square c.operator hF hc
  obtain ⟨hK, hKs⟩ := involutiveCorrection_compact G hgs hgi hgcpt
  let L : End c.space := G * cfc inverseSqrtCorrection (G * G - 1)
  let d := c.compactPerturb (kernelProjection c.operator) hk hks
  let e := d.compactPerturb L hK hKs
  have hec : cycleClass A e = cycleClass A c :=
    (compactPerturb_class d L hK hKs).trans (compactPerturb_class c _ hk hks)
  have heop : G + L = involutiveNormalization G :=
    (involutiveNormalization_eq G hgs hgi).symm
  refine ⟨e, hec, ?_, ?_, ?_⟩
  · change IsSelfAdjoint (G + L)
    rw [heop]
    exact involutiveNormalization_selfAdjoint G
  · change (G + L) * (G + L) = 1
    rw [heop]
    exact involutiveNormalization_sq G hgs hgi
  · change Commute (G + L) P
    rw [heop]
    exact hgcomm.cfc_real normalizedReal

theorem exists_represented_involutive_representative (c : OddCycle A) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧ IsSelfAdjoint d.operator ∧
      d.operator * d.operator = 1 ∧ Commute d.operator (d.representation 1) := by
  obtain ⟨d, hdc, hdself, hdQ⟩ := exists_represented_cutDown c
  obtain ⟨e, hed, heself, hesq, hecomm⟩ := exists_supported_involution d hdself hdQ
  exact ⟨e, hed.trans hdc, heself, hesq, hecomm⟩

end CoarseAssembly.Analytic

end

end OAI
