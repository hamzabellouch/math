import Mathlib

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BoundedIntertwiner
universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

 

theorem norm_map_le_of_gram_commutes (T : H →L[ℂ] K) (D : H →L[ℂ] H)
    (h : Commute (T.adjoint.comp T) D) (x : H) :
    ‖T (D x)‖ ≤ ‖D‖ * ‖T x‖ := by
  let G := T.adjoint.comp T
  have hG : 0 ≤ G := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  let S := CFC.sqrt G
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg G).isSelfAdjoint
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG
  have hSD : Commute S D := h.cfcₙ_nnreal NNReal.sqrt
  have hnorm (y : H) : ‖S y‖ = ‖T y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    congr 1
    calc
      inner ℂ (S y) (S y) = inner ℂ y (S.adjoint (S y)) :=
        (ContinuousLinearMap.adjoint_inner_right S y (S y)).symm
      _ = inner ℂ y (G y) := by
        rw [show S.adjoint = S from hS]
        exact congrArg (inner ℂ y) (congrArg (fun Z : H →L[ℂ] H => Z y) hSS)
      _ = inner ℂ (T y) (T y) := ContinuousLinearMap.adjoint_inner_right T y (T y)
  rw [← hnorm, ← hnorm]
  have he : S (D x) = D (S x) := congrArg (fun Z : H →L[ℂ] H => Z x) hSD.eq
  rw [he]
  exact D.le_opNorm _
end StronglyRationalVOA.BoundedIntertwiner

end

end OAI
