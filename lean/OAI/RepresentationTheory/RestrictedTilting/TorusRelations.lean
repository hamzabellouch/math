import OAI.RepresentationTheory.RestrictedTilting.RationalMatrices
import OAI.RepresentationTheory.RestrictedTilting.LaurentPolynomialSeparation

namespace OAI

namespace FiberFunctorProof
open scoped LaurentPolynomial BigOperators
universe u
variable (k : Type u) [Field k] [Infinite k]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (SL2 k) (ι → k)) (hρ : IsRational k ρ)

omit [Infinite k] in
lemma eval_laurent_invert (P : LaurentPolynomial k) (a : kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id k) a (LaurentPolynomial.invert P) =
      LaurentPolynomial.eval₂ (RingHom.id k) a⁻¹ P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T n c => simp [zpow_neg]

lemma rationalTorusMatrix_inverse :
    rationalTorusMatrix k ρ hρ * (rationalTorusMatrix k ρ hρ).map LaurentPolynomial.invert = 1 := by
  apply Matrix.ext
  intro i j
  apply laurent_eq_of_evals
  intro a
  have he : ((rationalTorusMatrix k ρ hρ).map LaurentPolynomial.invert).map
      (LaurentPolynomial.eval₂ (RingHom.id k) a) =
      (rationalTorusMatrix k ρ hρ).map (LaurentPolynomial.eval₂ (RingHom.id k) a⁻¹) := by
    ext r s
    exact eval_laurent_invert k _ a
  have hM : (rationalTorusMatrix k ρ hρ *
      (rationalTorusMatrix k ρ hρ).map LaurentPolynomial.invert).map
      (LaurentPolynomial.eval₂ (RingHom.id k) a) = 1 := by
    rw [Matrix.map_mul, he, eval_rationalTorusMatrix, eval_rationalTorusMatrix,
      ← LinearMap.toMatrix'_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
    simp only [map_one, LinearMap.toMatrix'_one]
  have hh := congrArg (fun A : Matrix ι ι k => A i j) hM
  simpa [Matrix.map_apply, Matrix.one_apply] using hh

lemma rational_torus_unipotent_laurent (t : k) :
    rationalTorusMatrix k ρ hρ * (LinearMap.toMatrix' (ρ (unipotent k t))).map LaurentPolynomial.C =
      polynomialMatrixEval (rationalUnipotentMatrix k ρ hρ)
        ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) *
      rationalTorusMatrix k ρ hρ := by
  apply Matrix.ext
  intro i j
  apply laurent_eq_of_evals
  intro a
  let ev : LaurentPolynomial k →ₐ[k] k :=
    ⟨LaurentPolynomial.eval₂ (RingHom.id k) a, fun c => LaurentPolynomial.eval₂_C _ _ c⟩
  have he : ((LinearMap.toMatrix' (ρ (unipotent k t))).map LaurentPolynomial.C).map ev =
      LinearMap.toMatrix' (ρ (unipotent k t)) := by
    ext r s
    exact LaurentPolynomial.eval₂_C _ _ _
  have hp : (polynomialMatrixEval (rationalUnipotentMatrix k ρ hρ)
      ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t)).map ev =
      LinearMap.toMatrix' (ρ (unipotent k ((a : k)^2*t))) := by
    rw [polynomialMatrixEval_map]
    have hev : ev ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) =
        (a : k)^2*t := by
      change LaurentPolynomial.eval₂ (RingHom.id k) a
        ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) = _
      simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
        RingHom.id_apply, zpow_ofNat, Units.val_pow_eq_pow_val]
    rw [hev]
    exact eval_rationalUnipotentMatrix k ρ hρ _
  have hM : ((rationalTorusMatrix k ρ hρ) *
      (LinearMap.toMatrix' (ρ (unipotent k t))).map LaurentPolynomial.C).map ev =
      (polynomialMatrixEval (rationalUnipotentMatrix k ρ hρ)
        ((LaurentPolynomial.T 2 : LaurentPolynomial k) * LaurentPolynomial.C t) *
        rationalTorusMatrix k ρ hρ).map ev := by
    rw [Matrix.map_mul, Matrix.map_mul, he, hp]
    change (rationalTorusMatrix k ρ hρ).map (LaurentPolynomial.eval₂ (RingHom.id k) a) * _ = _ *
      (rationalTorusMatrix k ρ hρ).map (LaurentPolynomial.eval₂ (RingHom.id k) a)
    rw [eval_rationalTorusMatrix, ← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_mul,
      ← map_mul, ← map_mul, diagonal_unipotent]
  exact congrArg (fun A : Matrix ι ι k => A i j) hM
end FiberFunctorProof

end OAI
