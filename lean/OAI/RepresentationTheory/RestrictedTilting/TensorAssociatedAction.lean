import OAI.RepresentationTheory.RestrictedTilting.TensorNumerator
import OAI.RepresentationTheory.RestrictedTilting.TensorPlaneTilting
import OAI.RepresentationTheory.RestrictedTilting.FormalAssociatedAction

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators Pointwise
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (β ι : Type u) [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
variable (τ : Representation k (SL2 k) (β → k))
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k
local notation "I" => MvPolynomial.idealOfVars (Fin 2) k
local notation "σ" => matrixTensorRepresentation τ (associatedSectionsRepresentation k ι ρ)
local notation "hσ" => matrixTensor_planeCompatible k τ (associatedSectionsRepresentation k ι ρ)
  (associatedSections_planeCompatible k ι ρ)
local notation "W" => tensorAssociatedNumerator k β ι ρ P hP d hd
variable [Module.Finite k ((β → associatedSectionsSubmodule k ι ρ) ⧸
  planeJetRelation (M := β → associatedSectionsSubmodule k ι ρ) k 1)]
local notation "T" => planeJetFD k σ hσ 1

noncomputable def formalTensorAssociatedCoordinates
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j) (v : T) :
    β × ι → planeCompletion k := completedCoordinates I W (formalPlaneSection k σ hσ s hs v)

lemma formalTensorAssociatedCoordinates_unipotent
    (s : (j : ℕ) → T ⟶ planeJetFD k σ hσ (j+1))
    (hs : ∀ j, s (j+1) ≫ planeJetTransitionHom k σ hσ (j+1) = s j)
    (t : k) (v : T) (b : β) (i : ι) :
    (PowerSeries.X : PowerSeries k)^(2*d) * formalLineMap k
      (formalTensorAssociatedCoordinates k β ι ρ P hP d hd τ s hs ((planeJetFD k σ hσ 1).ρ (unipotent k t) v) (b,i)) =
      ∑ c : β, ∑ j : ι, algebraMap k (PowerSeries k) (LinearMap.toMatrix' (τ (unipotent k t)) b c) *
        clearedPolynomial (P i j) (algebraMap k (PowerSeries k) t)
        ((PowerSeries.X : PowerSeries k)^2) d * formalLineMap k
          (formalTensorAssociatedCoordinates k β ι ρ P hP d hd τ s hs v (c,j)) := by
  let F : (β → N) →ₗ[A] A := (MvPolynomial.X 0 : A)^(2*d) • (LinearMap.proj (b,i)).comp W
  let G : (β → N) →ₗ[A] A := ∑ c : β, ∑ j : ι,
    (MvPolynomial.C (LinearMap.toMatrix' (τ (unipotent k t)) b c) *
      clearedPolynomial (P i j) (MvPolynomial.C t) ((MvPolynomial.X 0 : A)^2) d) •
        (LinearMap.proj (c,j)).comp W
  have he : ∀ f : β → N, linePolynomial k (F (σ (unipotent k t) f)) = linePolynomial k (G f) := by
    intro f
    simpa only [F,G,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
      LinearMap.proj_apply,smul_eq_mul,map_mul,map_pow,map_sum,
      show linePolynomial k (MvPolynomial.X 0) = Polynomial.X from by simp [linePolynomial],
      show ∀ c : k, linePolynomial k (MvPolynomial.C c) = Polynomial.C c from by intro c; simp [linePolynomial],
      linePolynomial_cleared] using tensorAssociatedNumerator_line_unipotent k β ι ρ P hP d hd τ t f b i
  have h := formalPlaneSection_line_action k σ hσ s hs (unipotent k t) F G he v
  simp only [F,G,completion_map_smul, LinearMap.sum_apply, completion_self_smul, map_mul, map_sum,
    map_pow, formalLineMap_X, formalLineMap_cleared] at h
  have hc (c : k) : formalLineMap k (algebraMap A (planeCompletion k) (MvPolynomial.C c)) =
      algebraMap k (PowerSeries k) c := by
    rw [MvPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  simpa only [formalTensorAssociatedCoordinates, completedCoordinates_apply, hc] using h
end FiberFunctorProof

end OAI
