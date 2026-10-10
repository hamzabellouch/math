import OAI.Topology.CoarseAssembly.EssentialToeplitz

namespace OAI

/-! # Multiplicativity of Toeplitz compression modulo compact operators -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem compact_commutator_mul (P U V : End H)
    (hU : IsCompactOperator (P * U - U * P : End H))
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    IsCompactOperator (P * (U * V) - (U * V) * P : End H) := by
  have he : P * (U * V) - (U * V) * P = (P * U - U * P) * V + U * (P * V - V * P) := by
    noncomm_ring
  rw [he]
  exact (compact_mul_right hU V).add (compact_mul_left hV U)

theorem compact_commutator_star_unitary (P U : End H)
    (hul : star U * U = 1) (hur : U * star U = 1)
    (hU : IsCompactOperator (P * U - U * P : End H)) :
    IsCompactOperator (P * star U - star U * P : End H) := by
  have he : P * star U - star U * P = -(star U * (P * U - U * P) * star U) := by
    calc
      _ = -(star U * P * (U * star U) - (star U * U) * P * star U) := by rw [hul, hur]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [he]
  exact (compact_mul_right (compact_mul_left hU (star U)) (star U)).neg

theorem toeplitzCompression_product_difference (P U V : End H) (hPP : P * P = P) :
    toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V) =
      P * U * (P * V - V * P) * P := by
  rw [toeplitzCompression_mul P U V hPP]
  have hlast : P * U * V * P * P = P * U * V * P := by rw [mul_assoc (P * U * V), hPP]
  simp only [toeplitzCompression, mul_sub, sub_mul, ← mul_assoc, hlast]
  abel

theorem toeplitzCompression_product_compact (P U V : End H) (hPP : P * P = P)
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    IsCompactOperator (toeplitzCompression P U * toeplitzCompression P V -
      toeplitzCompression P (U * V) : End H) := by
  rw [toeplitzCompression_product_difference P U V hPP]
  exact compact_mul_right (compact_mul_left hV (P * U)) P

theorem toeplitzCompression_index_mul (P U V : End H) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hVl : star V * V = 1) (hVr : V * star V = 1)
    (hU : IsCompactOperator (P * U - U * P : End H))
    (hV : IsCompactOperator (P * V - V * P : End H)) :
    (toeplitzCompression P (U * V)).toLinearMap.index =
      (toeplitzCompression P U).toLinearMap.index + (toeplitzCompression P V).toLinearMap.index := by
  have hUVl : star (U * V) * (U * V) = 1 := by
    calc
      _ = star V * (star U * U) * V := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hUl, mul_one, hVl]
  have hUVr : (U * V) * star (U * V) = 1 := by
    calc
      _ = U * (V * star V) * star U := by rw [star_mul]; noncomm_ring
      _ = 1 := by rw [hVr, mul_one, hUr]
  have hUV := compact_commutator_mul P U V hU hV
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects P (U * V) hP hPP hUVl hUVr hUV
  have hK := toeplitzCompression_product_compact P U V hPP hV
  have hKs : IsCompactOperator (star (toeplitzCompression P U * toeplitzCompression P V -
      toeplitzCompression P (U * V)) : End H) := by
    rw [star_sub, star_mul, toeplitzCompression_star P U hP,
      toeplitzCompression_star P V hP, toeplitzCompression_star P (U * V) hP, star_mul]
    exact toeplitzCompression_product_compact P (star V) (star U) hPP
      (compact_commutator_star_unitary P U hUl hUr hU)
  have hi := fredholmIndex_compactPerturb (toeplitzCompression P (U * V))
    (toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V)) hl hr hK hKs
  have he : toeplitzCompression P (U * V) +
      (toeplitzCompression P U * toeplitzCompression P V - toeplitzCompression P (U * V)) =
        toeplitzCompression P U * toeplitzCompression P V := by abel
  rw [he] at hi
  exact hi.trans ((toeplitzCompression_fredholm P U hP hPP hUl hUr hU).index_comp
    (toeplitzCompression_fredholm P V hP hPP hVl hVr hV))

end CoarseAssembly.Analytic

end

end OAI
