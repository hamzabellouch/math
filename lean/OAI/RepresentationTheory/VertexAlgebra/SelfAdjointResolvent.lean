import Mathlib

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
open Filter
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem imaginary_mem_resolvent {D : H →L[ℂ] H} (hD : IsSelfAdjoint D) :
    Complex.I ∈ resolventSet ℂ D := by
  rw [spectrum.mem_resolventSet_iff]
  by_contra h
  have he := hD.im_eq_zero_of_mem_spectrum (spectrum.mem_iff.mpr h)
  simp at he

 theorem norm_le_imaginary_shift {D : H →L[ℂ] H} (hD : IsSelfAdjoint D) (x : H) :
    ‖x‖ ≤ ‖((algebraMap ℂ (H →L[ℂ] H)) Complex.I - D) x‖ := by
  change ‖x‖ ≤ ‖Complex.I • x - D x‖
  have him := hD.isSymmetric.im_inner_self_apply x
  change (inner ℂ x (D x)).im = 0 at him
  have he : ‖Complex.I • x - D x‖ ^ 2 = ‖x‖ ^ 2 + ‖D x‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [norm_smul, Complex.norm_I, one_mul, inner_smul_left]
    simp [Complex.mul_re, him]
  have hsq : ‖x‖ ^ 2 ≤ ‖Complex.I • x - D x‖ ^ 2 := by
    rw [he]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

 

 theorem norm_resolvent_imaginary_le {D : H →L[ℂ] H} (hD : IsSelfAdjoint D) :
    ‖resolvent D Complex.I‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have he := congrArg (fun Q : H →L[ℂ] H => Q x)
    (Ring.mul_inverse_cancel ((algebraMap ℂ (H →L[ℂ] H)) Complex.I - D)
      (spectrum.mem_resolventSet_iff.mp (imaginary_mem_resolvent hD)))
  have hn := norm_le_imaginary_shift hD (resolvent D Complex.I x)
  change ‖resolvent D Complex.I x‖ ≤ ‖_‖ at hn
  change (((algebraMap ℂ (H →L[ℂ] H)) Complex.I - D) (resolvent D Complex.I x)) = x at he
  rw [he] at hn
  simpa only [one_mul] using hn

 

 theorem resolvent_imaginary_tendsto {ι : Type*} {F : Filter ι}
    {a : ι → H →L[ℂ] H} {D : H →L[ℂ] H}
    (ha : ∀ i, IsSelfAdjoint (a i)) (hD : IsSelfAdjoint D)
    (ht : ∀ x, Tendsto (fun i => a i x) F (nhds (D x))) (x : H) :
    Tendsto (fun i => resolvent (a i) Complex.I x) F
      (nhds (resolvent D Complex.I x)) := by
  have hi (i : ι) :
      ‖resolvent (a i) Complex.I x - resolvent D Complex.I x‖ ≤
      ‖a i (resolvent D Complex.I x) - D (resolvent D Complex.I x)‖ := by
    have he := congrArg (fun Q : H →L[ℂ] H => Q x)
      (spectrum.resolvent_sub_resolvent (imaginary_mem_resolvent (ha i))
        (imaginary_mem_resolvent hD))
    change resolvent (a i) Complex.I x - resolvent D Complex.I x =
      resolvent (a i) Complex.I (a i (resolvent D Complex.I x) - D (resolvent D Complex.I x)) at he
    rw [he]
    have hb := (resolvent (a i) Complex.I).le_opNorm
      (a i (resolvent D Complex.I x) - D (resolvent D Complex.I x))
    have hc := norm_resolvent_imaginary_le (ha i)
    exact hb.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hi
  simpa only [sub_self, norm_zero] using ((ht (resolvent D Complex.I x)).sub
    (tendsto_const_nhds (x := D (resolvent D Complex.I x)))).norm
end StronglyRationalVOA.BicommutantDensity

end

end OAI
