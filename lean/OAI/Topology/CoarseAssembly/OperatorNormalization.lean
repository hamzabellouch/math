import OAI.Topology.CoarseAssembly.InvolutiveNormalization

namespace OAI

/-! # A self-adjoint Fredholm operator is a compact perturbation of an involution -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem exists_compact_involution (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    ∃ N : End H, IsSelfAdjoint N ∧ N * N = 1 ∧
      IsCompactOperator (N - F : End H) ∧ IsCompactOperator (star (N - F) : End H) := by
  let G : End H := F + kernelProjection F
  have hgs : IsSelfAdjoint G := kernel_corrected_selfAdjoint F hF
  have hgi : IsUnit G := kernel_corrected_isUnit F hF hc
  have hgc : IsCompactOperator (G * G - 1 : End H) := kernel_corrected_compact_square F hF hc
  let N := involutiveNormalization G
  have hNs : IsSelfAdjoint N := involutiveNormalization_selfAdjoint G
  have hNsq : N * N = 1 := involutiveNormalization_sq G hgs hgi
  have hcor := (involutiveCorrection_compact G hgs hgi hgc).1
  have hNF : IsCompactOperator (N - F : End H) := by
    have he : N - F = kernelProjection F + G * cfc inverseSqrtCorrection (G * G - 1) := by
      dsimp only [N]
      rw [involutiveNormalization_eq G hgs hgi]
      dsimp only [G]
      abel
    rw [he]
    exact (kernelProjection_compact F hc).add hcor
  refine ⟨N, hNs, hNsq, hNF, ?_⟩
  rw [star_sub, hNs.star_eq, hF.star_eq]
  exact hNF

theorem compact_commutator_of_compact_change (F N U : End H)
    (hFN : IsCompactOperator (N - F : End H))
    (hFU : IsCompactOperator (F * U - U * F : End H)) :
    IsCompactOperator (N * U - U * N : End H) := by
  have he : N * U - U * N = (F * U - U * F) + (N - F) * U - U * (N - F) := by
    noncomm_ring
  rw [he]
  exact (hFU.add (compact_mul_right hFN U)).sub (compact_mul_left hFN U)

end CoarseAssembly.Analytic

end

end OAI
