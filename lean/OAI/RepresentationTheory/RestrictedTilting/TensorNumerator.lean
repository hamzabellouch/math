import OAI.RepresentationTheory.RestrictedTilting.PlaneMatrixTensor
import OAI.RepresentationTheory.RestrictedTilting.NumeratorAction

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (β ι : Type u) [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k
local notation "W" => associatedNumeratorLinear k ι ρ P hP d hd
local notation "Z" => associatedDenominatorLinear k ι ρ P hP d hd

noncomputable def tensorAssociatedNumerator : (β → N) →ₗ[A] (β × ι → A) :=
  LinearMap.pi fun bi => (LinearMap.proj bi.2).comp ((W).comp (LinearMap.proj bi.1))
noncomputable def tensorAssociatedDenominator : (β × ι → A) →ₗ[A] (β → N) :=
  LinearMap.pi fun b => (Z).comp (LinearMap.pi fun i => LinearMap.proj (b,i))

omit [Fintype β] [DecidableEq β] in
lemma tensorAssociatedNumerator_apply (v : β → N) (b : β) (i : ι) :
    tensorAssociatedNumerator k β ι ρ P hP d hd v (b,i) = W (v b) i := rfl
omit [Fintype β] [DecidableEq β] in
lemma tensorAssociatedDenominator_apply (v : β × ι → A) (b : β) :
    tensorAssociatedDenominator k β ι ρ P hP d hd v b = Z (fun i => v (b,i)) := rfl

omit [Fintype β] [DecidableEq β] in
lemma tensorAssociatedNumerator_denominator (v : β × ι → A) :
    tensorAssociatedNumerator k β ι ρ P hP d hd
      (tensorAssociatedDenominator k β ι ρ P hP d hd v) = (MvPolynomial.X 0 : A)^(d+d) • v := by
  funext bi
  exact congrFun (associatedNumerator_denominator k ι ρ P hP d hd (fun i => v (bi.1,i))) bi.2
omit [Fintype β] [DecidableEq β] in
lemma tensorAssociatedDenominator_numerator (v : β → N) :
    tensorAssociatedDenominator k β ι ρ P hP d hd
      (tensorAssociatedNumerator k β ι ρ P hP d hd v) = (MvPolynomial.X 0 : A)^(d+d) • v := by
  funext b
  exact associatedDenominator_numerator k ι ρ P hP d hd (v b)

variable (τ : Representation k (SL2 k) (β → k))
lemma tensorAssociatedNumerator_line_unipotent (t : k) (v : β → N) (b : β) (i : ι) :
    Polynomial.X^(2*d) * linePolynomial k
      (tensorAssociatedNumerator k β ι ρ P hP d hd
        (matrixTensorRepresentation τ (associatedSectionsRepresentation k ι ρ) (unipotent k t) v) (b,i)) =
      ∑ c : β, ∑ j : ι, Polynomial.C (LinearMap.toMatrix' (τ (unipotent k t)) b c) *
        clearedLineAction k (P i j) t d *
        linePolynomial k (tensorAssociatedNumerator k β ι ρ P hP d hd v (c,j)) := by
  simp only [tensorAssociatedNumerator_apply, matrixTensorRepresentation_apply,
    map_sum, LinearMap.map_smul_of_tower, Finset.sum_apply, Pi.smul_apply, map_smul]
  simp only [Algebra.smul_def, Polynomial.algebraMap_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_left_comm, associatedNumerator_line_unipotent k ι ρ P hP d hd t (v c) i,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]
  rfl
end FiberFunctorProof

end OAI
