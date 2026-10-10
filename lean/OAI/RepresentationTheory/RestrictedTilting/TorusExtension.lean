import OAI.RepresentationTheory.RestrictedTilting.TorusRelations

namespace OAI

namespace FiberFunctorProof
open scoped LaurentPolynomial
universe u v
variable {k : Type u} [Field k] [Infinite k]
variable {K : Type v} [Field K] [Algebra k K]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (SL2 k) (ι → k)) (hρ : IsRational k ρ)

noncomputable def laurentBaseEval (x : Kˣ) : LaurentPolynomial k →ₐ[k] K :=
  ⟨LaurentPolynomial.eval₂ (algebraMap k K) x,
    fun c => LaurentPolynomial.eval₂_C _ _ c⟩

noncomputable def torusMatrixAt (x : Kˣ) : Matrix ι ι K :=
  (rationalTorusMatrix k ρ hρ).map (laurentBaseEval x)

lemma torusMatrixAt_det_ne_zero (x : Kˣ) : (torusMatrixAt ρ hρ x).det ≠ 0 := by
  let Qinv := ((rationalTorusMatrix k ρ hρ).map LaurentPolynomial.invert).map
    (laurentBaseEval x)
  have he : torusMatrixAt ρ hρ x * Qinv = 1 := by
    rw [torusMatrixAt, ← Matrix.map_mul, rationalTorusMatrix_inverse, Matrix.map_one]
    all_goals simp only [map_zero, map_one]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact (mul_ne_zero_iff.mp (hd ▸ one_ne_zero)).1

lemma torusMatrixAt_unipotent (x : Kˣ) (t : k) :
    torusMatrixAt ρ hρ x * (LinearMap.toMatrix' (ρ (unipotent k t))).map (algebraMap k K) =
      polynomialMatrixEval (rationalUnipotentMatrix k ρ hρ) ((x : K)^2 * algebraMap k K t) *
        torusMatrixAt ρ hρ x := by
  have he := congrArg (fun A : Matrix ι ι (LaurentPolynomial k) => A.map (laurentBaseEval x))
    (rational_torus_unipotent_laurent k ρ hρ t)
  have hc : ((LinearMap.toMatrix' (ρ (unipotent k t))).map LaurentPolynomial.C).map
      (laurentBaseEval x) = (LinearMap.toMatrix' (ρ (unipotent k t))).map (algebraMap k K) := by
    apply Matrix.ext
    intro i j
    exact LaurentPolynomial.eval₂_C _ _ _
  have hx : laurentBaseEval x ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) =
      (x : K)^2 * algebraMap k K t := by
    change LaurentPolynomial.eval₂ (algebraMap k K) x
      ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) = _
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_ofNat, Units.val_pow_eq_pow_val]
  simpa only [Matrix.map_mul, hc, polynomialMatrixEval_map, hx, torusMatrixAt] using he

end FiberFunctorProof

end OAI
