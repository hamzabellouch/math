import OAI.RepresentationTheory.RestrictedTilting.LinearFormalComparison

namespace OAI

namespace FiberFunctorProof
open Matrix
open scoped TensorProduct Kronecker
universe u v
variable {k : Type u} [Field k] [Infinite k]
variable {K : Type v} [Field K] [Algebra k K]
variable {β ι : Type u} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable {T : Type u} [AddCommGroup T] [Module k T] [Module.Finite k T]

omit [Infinite k] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] in
lemma polynomialMatrixEval_kronecker (B : Matrix β β (Polynomial k))
    (P : Matrix ι ι (Polynomial k)) (t : K) :
    polynomialMatrixEval (B ⊗ₖ P) t = polynomialMatrixEval B t ⊗ₖ polynomialMatrixEval P t := by
  ext i j
  exact map_mul (Polynomial.aeval t) _ _

 

theorem tensor_linear_formal_comparison
    (σ : Representation k (SL2 k) T) (hσ : IsRational k σ)
    (τ : Representation k (SL2 k) (β → k)) (hτ : IsRational k τ)
    (P : Matrix ι ι (Polynomial k)) (x : K) (hx : x ≠ 0)
    (F : (K ⊗[k] T) ≃ₗ[K] (β × ι → K))
    (hF : ∀ t : k, ∀ v : T,
      F (1 ⊗ₜ[k] σ (unipotent k t) v) =
        ((LinearMap.toMatrix' (τ (unipotent k t))).map (algebraMap k K) ⊗ₖ
          polynomialMatrixEval P (algebraMap k K t / x^2)) *ᵥ F (1 ⊗ₜ[k] v)) :
    ∃ E : T ≃ₗ[k] (β × ι → k), ∀ t : k, ∀ v : T,
      E (σ (unipotent k t) v) =
        (LinearMap.toMatrix' (τ (unipotent k t)) ⊗ₖ polynomialMatrixEval P t) *ᵥ E v := by
  let xU : Kˣ := Units.mk0 x hx
  let Q := torusMatrixAt τ hτ xU⁻¹
  let L : Matrix (β × ι) (β × ι) K := Q ⊗ₖ (1 : Matrix ι ι K)
  have hL : L.det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
    exact pow_ne_zero _ (torusMatrixAt_det_ne_zero τ hτ xU⁻¹)
  let E₀ := Matrix.toLinearEquiv (Pi.basisFun K (β × ι)) L (isUnit_iff_ne_zero.mpr hL)
  have hE₀ (v : β × ι → K) : E₀ v = L *ᵥ v := by
    rw [Matrix.toLinearEquiv_apply]
    rfl
  let B := rationalUnipotentMatrix k τ hτ
  have hcorr (t : k) : L * ((LinearMap.toMatrix' (τ (unipotent k t))).map (algebraMap k K) ⊗ₖ
      polynomialMatrixEval P (algebraMap k K t / x^2)) =
      polynomialMatrixEval (B ⊗ₖ P) (algebraMap k K t / x^2) * L := by
    rw [polynomialMatrixEval_kronecker]
    change (Q ⊗ₖ (1 : Matrix ι ι K)) * _ = _ * (Q ⊗ₖ (1 : Matrix ι ι K))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    have he := torusMatrixAt_unipotent τ hτ xU⁻¹ t
    have hp : ((xU⁻¹ : Kˣ) : K)^2 * algebraMap k K t = algebraMap k K t / x^2 := by
      change (x⁻¹)^2 * _ = _
      rw [inv_pow, div_eq_mul_inv, mul_comm]
    rw [hp] at he
    rw [he]
  obtain ⟨E,hE⟩ := linear_formal_comparison σ hσ (B ⊗ₖ P) x hx (F.trans E₀) (by
    intro t v
    simp only [LinearEquiv.trans_apply, hE₀]
    rw [hF, Matrix.mulVec_mulVec, hcorr, ← Matrix.mulVec_mulVec])
  refine ⟨E, fun t v => ?_⟩
  have hB : polynomialMatrixEval B t = LinearMap.toMatrix' (τ (unipotent k t)) :=
    eval_rationalUnipotentMatrix k τ hτ t
  simpa only [polynomialMatrixEval_kronecker, hB] using hE t v
end FiberFunctorProof

end OAI
