import OAI.Topology.CoarseAssembly.ToeplitzProductIndex

namespace OAI

/-! # Additivity of the essentially self-adjoint Toeplitz index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem essentialToeplitz_index_normalize (F N U : End H)
    (hF : IsSelfAdjoint F) (hN : IsSelfAdjoint N) (hNN : N * N = 1)
    (hNF : IsCompactOperator (N - F : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hFU : IsCompactOperator (F * U - U * F : End H)) :
    (toeplitzCompression (positiveProjection F) U).toLinearMap.index =
      (toeplitzCompression (positiveProjection N) U).toLinearMap.index := by
  have hNU := compact_commutator_of_compact_change F N U hNF hFU
  have hQU : IsCompactOperator (positiveProjection N * U - U * positiveProjection N : End H) := by
    rw [positiveProjection_commutator]
    exact hNU.smul (1 / 2 : ℝ)
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects (positiveProjection N) U
    (positiveProjection_selfAdjoint N hN) (positiveProjection_sq N hNN) hUl hUr hQU
  have hPQ : IsCompactOperator (positiveProjection F - positiveProjection N : End H) := by
    rw [positiveProjection_sub, show F - N = -(N - F) by abel]
    exact hNF.neg.smul (1 / 2 : ℝ)
  have hi := fredholmIndex_compactPerturb (toeplitzCompression (positiveProjection N) U)
    (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U)
    hl hr (compact_toeplitz_sub _ _ _ hPQ)
    (compact_star_toeplitz_sub _ _ _ (positiveProjection_selfAdjoint F hF)
      (positiveProjection_selfAdjoint N hN) hPQ)
  have he : toeplitzCompression (positiveProjection N) U +
      (toeplitzCompression (positiveProjection F) U - toeplitzCompression (positiveProjection N) U) =
        toeplitzCompression (positiveProjection F) U := by abel
  rw [he] at hi
  exact hi.symm

theorem essentialToeplitz_index_mul (F U V : End H) (hF : IsSelfAdjoint F)
    (hFF : IsCompactOperator (F * F - 1 : End H))
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hVl : star V * V = 1) (hVr : V * star V = 1)
    (hU : IsCompactOperator (F * U - U * F : End H))
    (hV : IsCompactOperator (F * V - V * F : End H)) :
    (toeplitzCompression (positiveProjection F) (U * V)).toLinearMap.index =
      (toeplitzCompression (positiveProjection F) U).toLinearMap.index +
      (toeplitzCompression (positiveProjection F) V).toLinearMap.index := by
  obtain ⟨N, hN, hNN, hNF, _⟩ := exists_compact_involution F hF hFF
  have hUVl : star (U * V) * (U * V) = 1 := by
    calc
      _ = star V * (star U * U) * V := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hUl, mul_one, hVl]
  have hUVr : (U * V) * star (U * V) = 1 := by
    calc
      _ = U * (V * star V) * star U := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hVr, mul_one, hUr]
  rw [essentialToeplitz_index_normalize F N (U * V) hF hN hNN hNF hUVl hUVr
    (compact_commutator_mul F U V hU hV)]
  rw [essentialToeplitz_index_normalize F N U hF hN hNN hNF hUl hUr hU,
    essentialToeplitz_index_normalize F N V hF hN hNN hNF hVl hVr hV]
  apply toeplitzCompression_index_mul _ _ _ (positiveProjection_selfAdjoint N hN)
    (positiveProjection_sq N hNN) hUl hUr hVl hVr
  · rw [positiveProjection_commutator]
    exact (compact_commutator_of_compact_change F N U hNF hU).smul (1 / 2 : ℝ)
  · rw [positiveProjection_commutator]
    exact (compact_commutator_of_compact_change F N V hNF hV).smul (1 / 2 : ℝ)

end CoarseAssembly.Analytic

end

end OAI
