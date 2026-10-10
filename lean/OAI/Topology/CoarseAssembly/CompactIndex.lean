import OAI.Topology.CoarseAssembly.CycleIndex

namespace OAI

/-! # Compact perturbation invariance of the Fredholm index

The compactness of both the perturbation and its adjoint keeps the straight
line path unitary modulo compact operators. Local constancy of the Fredholm
index then gives invariance, without a spectral choice of normalization.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem essentialUnitary_compactPerturb (T K : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H))
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End H)) :
    IsCompactOperator (star (T + K) * (T + K) - 1 : End H) ∧
      IsCompactOperator ((T + K) * star (T + K) - 1 : End H) := by
  constructor
  · have he : star (T + K) * (T + K) - 1 =
        (star T * T - 1) + star T * K + star K * T + star K * K := by
      rw [star_add]
      noncomm_ring
    rw [he]
    exact ((hl.add (compact_mul_left hK _)).add (compact_mul_right hKs _)).add
      (compact_mul_left hK _)
  · have he : (T + K) * star (T + K) - 1 =
        (T * star T - 1) + T * star K + K * star T + K * star K := by
      rw [star_add]
      noncomm_ring
    rw [he]
    exact ((hr.add (compact_mul_left hKs _)).add (compact_mul_right hK _)).add
      (compact_mul_left hKs _)

theorem fredholmIndex_compactPerturb (T K : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H))
    (hK : IsCompactOperator K) (hKs : IsCompactOperator (star K : End H)) :
    T.toLinearMap.index = (T + K).toLinearMap.index := by
  have hf (t : Interval) : (T + (t : ℝ) • K).IsFredholm := by
    obtain ⟨hl', hr'⟩ := essentialUnitary_compactPerturb T ((t : ℝ) • K) hl hr
      (hK.smul _) (compact_star_real_smul hKs _)
    exact isFredholm_of_compact_essential_unitary _ hl' hr'
  have hh := fredholmIndex_homotopy (fun t : Interval => T + (t : ℝ) • K)
    (continuous_const.add (continuous_subtype_val.smul continuous_const)) hf
  simpa only [start, finish, zero_smul, one_smul, add_zero] using hh

end CoarseAssembly.Analytic

end

end OAI
