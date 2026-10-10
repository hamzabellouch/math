import OAI.Topology.CoarseAssembly.OperatorNormalization
import OAI.Topology.CoarseAssembly.CompactIndex

namespace OAI

/-! # Toeplitz Fredholmness before choosing an involution

A self-adjoint operator with compact square defect suffices. This lets the
index be defined using the explicit, continuous cut-down operator.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem positiveProjection_sub (F G : End H) :
    positiveProjection F - positiveProjection G = (1 / 2 : ℝ) • (F - G) := by
  unfold positiveProjection
  module

theorem compact_toeplitz_sub (P Q U : End H) (hPQ : IsCompactOperator (P - Q : End H)) :
    IsCompactOperator (toeplitzCompression P U - toeplitzCompression Q U : End H) := by
  have he : toeplitzCompression P U - toeplitzCompression Q U =
      (P - Q) * U * P + Q * U * (P - Q) - (P - Q) := by
    unfold toeplitzCompression
    noncomm_ring
  rw [he]
  exact ((compact_mul_right (compact_mul_right hPQ U) P).add
    (compact_mul_left hPQ (Q * U))).sub hPQ

theorem compact_star_toeplitz_sub (P Q U : End H) (hP : IsSelfAdjoint P)
    (hQ : IsSelfAdjoint Q) (hPQ : IsCompactOperator (P - Q : End H)) :
    IsCompactOperator (star (toeplitzCompression P U - toeplitzCompression Q U) : End H) := by
  rw [star_sub, toeplitzCompression_star P U hP, toeplitzCompression_star Q U hQ]
  exact compact_toeplitz_sub P Q (star U) hPQ

theorem essentialToeplitz_compact_defects (F U : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (F * U - U * F : End H)) :
    IsCompactOperator (star (toeplitzCompression (positiveProjection F) U) *
      toeplitzCompression (positiveProjection F) U - 1 : End H) ∧
    IsCompactOperator (toeplitzCompression (positiveProjection F) U *
      star (toeplitzCompression (positiveProjection F) U) - 1 : End H) := by
  obtain ⟨N, hNs, hNsq, hNF, _⟩ := exists_compact_involution F hF hc
  have hNU := compact_commutator_of_compact_change F N U hNF hcomm
  have hQU : IsCompactOperator (positiveProjection N * U - U * positiveProjection N : End H) := by
    rw [positiveProjection_commutator]
    exact hNU.smul (1 / 2 : ℝ)
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects (positiveProjection N) U
    (positiveProjection_selfAdjoint N hNs) (positiveProjection_sq N hNsq) hUl hUr hQU
  have hPQ : IsCompactOperator (positiveProjection F - positiveProjection N : End H) := by
    rw [positiveProjection_sub, show F - N = -(N - F) by abel]
    exact hNF.neg.smul (1 / 2 : ℝ)
  have hd := compact_toeplitz_sub (positiveProjection F) (positiveProjection N) U hPQ
  have hds := compact_star_toeplitz_sub (positiveProjection F) (positiveProjection N) U
    (positiveProjection_selfAdjoint F hF) (positiveProjection_selfAdjoint N hNs) hPQ
  have h := essentialUnitary_compactPerturb (toeplitzCompression (positiveProjection N) U)
    (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U)
    hl hr hd hds
  have he : toeplitzCompression (positiveProjection N) U +
      (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U) =
      toeplitzCompression (positiveProjection F) U := by abel
  rwa [he] at h

end CoarseAssembly.Analytic

end

end OAI
