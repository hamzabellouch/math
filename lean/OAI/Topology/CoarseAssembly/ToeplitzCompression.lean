import OAI.Topology.CoarseAssembly.FredholmParametrix

namespace OAI

/-! # Fredholmness of scalar-unitary Toeplitz compressions -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def toeplitzCompression (P U : End H) : End H := P * U * P + (1 - P)

theorem toeplitzCompression_star (P U : End H) (hP : IsSelfAdjoint P) :
    star (toeplitzCompression P U) = toeplitzCompression P (star U) := by
  simp only [toeplitzCompression, star_add, star_mul, star_sub, star_one, hP.star_eq, mul_assoc]

theorem toeplitzCompression_mul (P U V : End H) (hP : P * P = P) :
    toeplitzCompression P U * toeplitzCompression P V = P * U * P * V * P + (1 - P) := by
  have hright (A : End H) : A * P * P = A * P := by rw [mul_assoc, hP]
  simp only [toeplitzCompression, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
    ← mul_assoc, hright, hP]
  abel

theorem toeplitzCompression_left_defect (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hU : star U * U = 1) :
    star (toeplitzCompression P U) * toeplitzCompression P U - 1 =
      P * star U * (P * U - U * P) * P := by
  rw [toeplitzCompression_star P U hP, toeplitzCompression_mul P (star U) U hPP]
  have he : P * star U * U * P * P = P := by
    rw [mul_assoc P (star U) U, hU, mul_one, hPP, hPP]
  simp only [mul_sub, sub_mul, ← mul_assoc, he]
  abel

theorem toeplitzCompression_compact_defects (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (P * U - U * P : End H)) :
    IsCompactOperator (star (toeplitzCompression P U) * toeplitzCompression P U - 1 : End H) ∧
      IsCompactOperator (toeplitzCompression P U * star (toeplitzCompression P U) - 1 : End H) := by
  have hcommStar : IsCompactOperator (P * star U - star U * P : End H) := by
    have he : P * star U - star U * P = -(star U * (P * U - U * P) * star U) := by
      symm
      calc
        _ = -(star U * P * (U * star U) - (star U * U) * P * star U) := by noncomm_ring
        _ = _ := by rw [hUr, hUl]; noncomm_ring
    rw [he]
    exact (compact_mul_right (compact_mul_left hcomm (star U)) (star U)).neg
  constructor
  · rw [toeplitzCompression_left_defect P U hP hPP hUl]
    exact compact_mul_right (compact_mul_left hcomm (P * star U)) P
  · have he := toeplitzCompression_left_defect P (star U) hP hPP (by simpa only [star_star] using hUr)
    rw [star_star, ← toeplitzCompression_star P U hP, star_star] at he
    rw [he]
    exact compact_mul_right (compact_mul_left hcommStar (P * U)) P

theorem toeplitzCompression_fredholm (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : IsCompactOperator (P * U - U * P : End H)) :
    (toeplitzCompression P U).IsFredholm := by
  obtain ⟨hl, hr⟩ := toeplitzCompression_compact_defects P U hP hPP hUl hUr hcomm
  exact isFredholm_of_compact_essential_unitary _ hl hr

theorem toeplitzCompression_unitary (P U : End H) (hP : IsSelfAdjoint P)
    (hPP : P * P = P) (hUl : star U * U = 1) (hUr : U * star U = 1)
    (hcomm : Commute P U) :
    star (toeplitzCompression P U) * toeplitzCompression P U = 1 ∧
      toeplitzCompression P U * star (toeplitzCompression P U) = 1 := by
  have hc : P * U - U * P = 0 := sub_eq_zero.mpr hcomm.eq
  have hcs : P * star U - star U * P = 0 := by
    apply sub_eq_zero.mpr
    simpa only [star_mul, hP.star_eq] using (congrArg star hcomm.eq).symm
  constructor
  · apply sub_eq_zero.mp
    rw [toeplitzCompression_left_defect P U hP hPP hUl, hc, mul_zero, zero_mul]
  · apply sub_eq_zero.mp
    have he := toeplitzCompression_left_defect P (star U) hP hPP
      (by simpa only [star_star] using hUr)
    rw [star_star, ← toeplitzCompression_star P U hP, star_star, hcs, mul_zero, zero_mul] at he
    exact he

end CoarseAssembly.Analytic

end

end OAI
