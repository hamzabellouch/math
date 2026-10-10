import OAI.Topology.CoarseAssembly.ScalarCutDown
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! # Normalization preserving the represented scalar subspace -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem kernelProjection_complement (F P : End H) (hF : IsSelfAdjoint F)
    (hQ : F * (1 - P) = 1 - P) : kernelProjection F * (1 - P) = 0 := by
  calc
    kernelProjection F * (1 - P) = kernelProjection F * (F * (1 - P)) := by rw [hQ]
    _ = (kernelProjection F * F) * (1 - P) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [kernelProjection_mul F hF, zero_mul]

theorem commute_of_complement (F P : End H) (hF : IsSelfAdjoint F) (hP : IsSelfAdjoint P)
    (hQ : F * (1 - P) = 1 - P) : Commute F P := by
  have hQ' : (1 - P) * F = 1 - P := by
    have h := congrArg star hQ
    simpa only [star_mul, star_sub, star_one, hF.star_eq, hP.star_eq] using h
  have h1 : F - F * P = 1 - P := by simpa only [mul_sub, mul_one] using hQ
  have h2 : F - P * F = 1 - P := by simpa only [sub_mul, one_mul] using hQ'
  have h := congrArg (fun T : End H => F - T) (h1.trans h2.symm)
  exact (by simpa only [sub_sub_cancel] using h : F * P = P * F)

theorem supported_scalar_cycleClass_zero (c : OddCycle ℂ) (hF : IsSelfAdjoint c.operator)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1) :
    cycleClass ℂ c = 0 := by
  let P : End c.space := c.representation 1
  have hc := supported_square_compact c hQ
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
    commute_of_complement G P hgs (scalar_projection_selfAdjoint c) hgQ
  have hgcpt : IsCompactOperator (G * G - 1 : End c.space) :=
    kernel_corrected_compact_square c.operator hF hc
  obtain ⟨hK, hKs⟩ := involutiveCorrection_compact G hgs hgi hgcpt
  let L : End c.space := G * cfc inverseSqrtCorrection (G * G - 1)
  let d := c.compactPerturb (kernelProjection c.operator) hk hks
  let e := d.compactPerturb L hK hKs
  have hec : cycleClass ℂ e = cycleClass ℂ c :=
    (compactPerturb_class d L hK hKs).trans (compactPerturb_class c _ hk hks)
  have heop : G + L = involutiveNormalization G :=
    (involutiveNormalization_eq G hgs hgi).symm
  have hedeg : e.Degenerate := by
    change (∀ z, (G + L) * c.representation z - c.representation z * (G + L) = 0) ∧
      (∀ z, ((G + L) * (G + L) - 1) * c.representation z = 0) ∧
      (∀ z, (star (G + L) - (G + L)) * c.representation z = 0)
    rw [heop]
    refine ⟨?_, ?_, ?_⟩
    · intro z
      have hecomm : Commute (involutiveNormalization G) P := hgcomm.cfc_real normalizedReal
      rw [scalar_representation, mul_smul_comm, smul_mul_assoc, hecomm.eq, sub_self]
    · intro z
      rw [involutiveNormalization_sq G hgs hgi, sub_self, zero_mul]
    · intro z
      rw [(involutiveNormalization_selfAdjoint G).star_eq, sub_self, zero_mul]
  exact hec.symm.trans (degenerate_zero e hedeg)

theorem scalar_cycleClass_zero (c : OddCycle ℂ) : cycleClass ℂ c = 0 := by
  obtain ⟨d, hdc, hdself, hdQ⟩ := exists_supported_scalar_representative c
  exact hdc.symm.trans (supported_scalar_cycleClass_zero d hdself hdQ)

end CoarseAssembly.Analytic

end

end OAI
