import OAI.RepresentationTheory.RestrictedTilting.TensorAssociatedAction
import OAI.RepresentationTheory.RestrictedTilting.FormalAssociatedIso

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory Matrix
open scoped TensorProduct BigOperators Pointwise Kronecker
universe u
variable (k : Type u) [Field k] [Infinite k]
attribute [local instance 1100] HahnSeries.instAlgebra
variable (β ι : Type u) [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
variable (τ : Representation k (SL2 k) (β → k))
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "H" => planeCompletion k
local notation "K" => LaurentSeries k
local notation "σ" => matrixTensorRepresentation τ (associatedSectionsRepresentation k ι ρ)
local notation "hσ" => matrixTensor_planeCompatible k τ (associatedSectionsRepresentation k ι ρ)
  (associatedSections_planeCompatible k ι ρ)
local notation "W" => tensorAssociatedNumerator k β ι ρ P hP d hd
local notation "Z" => tensorAssociatedDenominator k β ι ρ P hP d hd
local notation "hx" => pi_regular_x k (β := β) (And.left (associatedSections_regular k ι ρ P hP))
local notation "hy" => pi_regular_y k (β := β) (And.right (associatedSections_regular k ι ρ P hP))
variable [Module.Finite k ((β → associatedSectionsSubmodule k ι ρ) ⧸
  planeJetRelation (M := β → associatedSectionsSubmodule k ι ρ) k 1)]
local notation "T" => planeJetFD k σ hσ 1

noncomputable def tensorAssociatedFieldTrivialization
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j) : (K ⊗[k] T) ≃ₗ[K] (β × ι → K) := by
  letI : Algebra H K := (formalLineFieldMap k).toRingHom.toAlgebra
  exact fieldCoordinateTrivialization (formalPlaneTrivialization k σ hσ s hs0 hs hx hy)
    (completedCoordinates I W) (completedDenominator I Z)
    (algebraMap A H ((MvPolynomial.X 0)^ (d+d)))
    (completedCoordinates_denominator I W Z _ (tensorAssociatedNumerator_denominator k β ι ρ P hP d hd))
    (completedDenominator_coordinates I W Z _ (tensorAssociatedDenominator_numerator k β ι ρ P hP d hd))
    (by
      change formalLineFieldMap k (algebraMap A H ((MvPolynomial.X 0)^(d+d))) ≠ 0
      rw [map_pow, map_pow]
      exact pow_ne_zero _ (formalLineFieldMap_X_ne_zero k))

lemma tensorAssociatedFieldTrivialization_one
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (v : T) (i : β × ι) :
    tensorAssociatedFieldTrivialization k β ι ρ P hP d hd τ s hs0 hs (1 ⊗ₜ[k] v) i =
      HahnSeries.ofPowerSeries ℤ k
        (formalLineMap k (formalTensorAssociatedCoordinates k β ι ρ P hP d hd τ s hs v i)) := by
  let : Algebra H K := (formalLineFieldMap k).toRingHom.toAlgebra
  dsimp only [tensorAssociatedFieldTrivialization]
  rw [fieldCoordinateTrivialization_one, formalPlaneTrivialization_one_tmul]
  rfl

lemma tensorAssociatedFieldTrivialization_unipotent_one
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1)) (hs0 : s 0 = 𝟙 _)
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (t : k) (v : T) :
    tensorAssociatedFieldTrivialization k β ι ρ P hP d hd τ s hs0 hs
      (1 ⊗ₜ[k] ((planeJetFD k σ hσ 1).ρ (unipotent k t) v)) =
      ( (LinearMap.toMatrix' (τ (unipotent k t))).map (algebraMap k K) ⊗ₖ
        polynomialMatrixEval P (algebraMap k K t / (formalLineParameter k)^2)) *ᵥ
        tensorAssociatedFieldTrivialization k β ι ρ P hP d hd τ s hs0 hs (1 ⊗ₜ[k] v) := by
  apply funext
  rintro ⟨b,i⟩
  have he := congrArg (HahnSeries.ofPowerSeriesAlg ℤ k)
    (formalTensorAssociatedCoordinates_unipotent k β ι ρ P hP d hd τ s hs t v b i)
  simp only [map_mul, map_pow, map_sum] at he
  have hc (j : ι) : (HahnSeries.ofPowerSeriesAlg ℤ k)
      (clearedPolynomial (P i j) (algebraMap k (PowerSeries k) t)
        ((PowerSeries.X : PowerSeries k)^2) d) =
      (formalLineParameter k)^(2*d) *
        Polynomial.aeval (algebraMap k K t / (formalLineParameter k)^2) (P i j) := by
    have hc := clearedPolynomial_eval (HahnSeries.ofPowerSeriesAlg ℤ k) (P i j)
      (algebraMap k (PowerSeries k) t) ((PowerSeries.X : PowerSeries k)^2) d (hd i j)
      (by
        rw [map_pow]
        exact pow_ne_zero 2 (formalLineParameter_ne_zero k))
    simpa only [map_pow, AlgHom.commutes, ofPowerSeriesAlg_apply_eq, formalLineParameter, ← pow_mul, div_eq_mul_inv] using hc
  simp only [hc, AlgHom.commutes] at he
  simp only [mul_left_comm (algebraMap k K _) ((formalLineParameter k)^(2*d)),
    mul_assoc, ← Finset.mul_sum] at he
  apply mul_left_cancel₀ (pow_ne_zero (2*d) (formalLineParameter_ne_zero k))
  simpa only [tensorAssociatedFieldTrivialization_one, Matrix.mulVec, dotProduct, polynomialMatrixEval,
    formalLineParameter, ofPowerSeriesAlg_apply_eq, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.map_apply, mul_assoc, ← Finset.mul_sum] using he
end FiberFunctorProof

end OAI
