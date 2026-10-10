import Mathlib

namespace OAI

 

noncomputable section

open scoped BigOperators
open Polynomial

namespace FiberFunctorProof

universe u v

variable {k : Type u} [Field k]
variable (H : AddSubgroup k) [Fintype H]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

 
def liftEntry (ρ : Multiplicative H →* Matrix ι ι k) (i j : ι) : k[X] := by
  classical
  exact Lagrange.interpolate Finset.univ (fun h : H => (h : k))
    (fun h => ρ (Multiplicative.ofAdd h) i j)

 
def liftMatrix (ρ : Multiplicative H →* Matrix ι ι k) (t : k) : Matrix ι ι k :=
  fun i j => (liftEntry H ρ i j).eval t

lemma liftEntry_degree (ρ : Multiplicative H →* Matrix ι ι k) (i j : ι) :
    (liftEntry H ρ i j).degree < (Fintype.card H : WithBot ℕ) := by
  classical
  simpa only [liftEntry, Finset.card_univ] using Lagrange.degree_interpolate_lt
    (s := Finset.univ) (v := fun h : H => (h : k))
    (fun h : H => ρ (Multiplicative.ofAdd h) i j) Subtype.val_injective.injOn

@[simp]
lemma liftMatrix_at_subgroup (ρ : Multiplicative H →* Matrix ι ι k) (h : H) :
    liftMatrix H ρ (h : k) = ρ (Multiplicative.ofAdd h) := by
  classical
  ext i j
  exact Lagrange.eval_interpolate_at_node
    (fun h : H => ρ (Multiplicative.ofAdd h) i j)
    Subtype.val_injective.injOn (Finset.mem_univ h)

lemma polynomial_degree_translate (f : k[X]) (t : k) :
    (f.comp (X + C t)).degree = f.degree := by
  rw [Polynomial.degree_comp (by simp), Polynomial.degree_X_add_C, mul_one]

lemma polynomial_degree_mul_constant_le (f : k[X]) (a : k) :
    (f * C a).degree ≤ f.degree := by
  by_cases ha : a = 0
  · simp [ha]
  · exact le_of_eq (Polynomial.degree_mul_C ha)

lemma polynomial_degree_constant_mul_le (f : k[X]) (a : k) :
    (C a * f).degree ≤ f.degree := by
  simpa [mul_comm] using polynomial_degree_mul_constant_le f a

lemma polynomial_degree_sum_lt {J : Type*} (s : Finset J) (f : J → k[X]) (b : ℕ)
    (h : ∀ i ∈ s, (f i).degree < (b : WithBot ℕ)) :
    (∑ i ∈ s, f i).degree < (b : WithBot ℕ) := by
  rw [← Polynomial.mem_degreeLT]
  exact Submodule.sum_mem _ fun i hi => Polynomial.mem_degreeLT.mpr (h i hi)

 
lemma liftMatrix_add_subgroup (ρ : Multiplicative H →* Matrix ι ι k) (t : k) (h : H) :
    liftMatrix H ρ (t + (h : k)) = liftMatrix H ρ t * ρ (Multiplicative.ofAdd h) := by
  classical
  ext i j
  have hp : (liftEntry H ρ i j).comp (X + C (h : k)) =
      ∑ a : ι, liftEntry H ρ i a * C (ρ (Multiplicative.ofAdd h) a j) := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (v := fun g : H => (g : k)) Finset.univ Subtype.val_injective.injOn ?_ ?_ ?_
    · simpa only [polynomial_degree_translate, Finset.card_univ] using liftEntry_degree H ρ i j
    · exact polynomial_degree_sum_lt _ _ _ fun a _ =>
        lt_of_le_of_lt (polynomial_degree_mul_constant_le _ _) (by
          simpa only [Finset.card_univ] using liftEntry_degree H ρ i a)
    · intro g _
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul]
      change liftMatrix H ρ ((g : k) + (h : k)) i j =
        (liftMatrix H ρ (g : k) * ρ (Multiplicative.ofAdd h)) i j
      rw [← AddSubgroup.coe_add, liftMatrix_at_subgroup, liftMatrix_at_subgroup]
      exact congrArg (fun M : Matrix ι ι k => M i j) (ρ.map_mul _ _)
  have hp' := congrArg (Polynomial.eval t) hp
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    liftMatrix, Matrix.mul_apply] using hp'

 
lemma liftMatrix_add (ρ : Multiplicative H →* Matrix ι ι k) (s t : k) :
    liftMatrix H ρ (s + t) = liftMatrix H ρ s * liftMatrix H ρ t := by
  classical
  ext i j
  have hp : (liftEntry H ρ i j).comp (X + C s) =
      ∑ a : ι, C (liftMatrix H ρ s i a) * liftEntry H ρ a j := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (v := fun g : H => (g : k)) Finset.univ Subtype.val_injective.injOn ?_ ?_ ?_
    · simpa only [polynomial_degree_translate, Finset.card_univ] using liftEntry_degree H ρ i j
    · exact polynomial_degree_sum_lt _ _ _ fun a _ =>
        lt_of_le_of_lt (polynomial_degree_constant_mul_le _ _) (by
          simpa only [Finset.card_univ] using liftEntry_degree H ρ a j)
    · intro g _
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul]
      change liftMatrix H ρ ((g : k) + s) i j =
        (liftMatrix H ρ s * liftMatrix H ρ (g : k)) i j
      rw [add_comm, liftMatrix_add_subgroup, liftMatrix_at_subgroup]
  have hp' := congrArg (Polynomial.eval t) hp
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    liftMatrix, Matrix.mul_apply, add_comm t s] using hp'

@[simp]
lemma liftMatrix_zero (ρ : Multiplicative H →* Matrix ι ι k) :
    liftMatrix H ρ 0 = 1 := by
  simpa using liftMatrix_at_subgroup H ρ (0 : H)

 
def extendedRepresentation (ρ : Multiplicative H →* Matrix ι ι k) :
    Multiplicative k →* Matrix ι ι k where
  toFun t := liftMatrix H ρ t.toAdd
  map_one' := liftMatrix_zero H ρ
  map_mul' s t := liftMatrix_add H ρ s.toAdd t.toAdd

 

theorem finite_additive_representation_lift
    (ρ : Multiplicative H →* Matrix ι ι k) :
    ∃ σ : Multiplicative k →* Matrix ι ι k,
      (∀ h : H, σ (Multiplicative.ofAdd (h : k)) = ρ (Multiplicative.ofAdd h)) ∧
      (∀ i j : ι, ∃ f : k[X], f.degree < (Fintype.card H : WithBot ℕ) ∧
        ∀ t : k, σ (Multiplicative.ofAdd t) i j = f.eval t) := by
  refine ⟨extendedRepresentation H ρ, ?_, ?_⟩
  · exact liftMatrix_at_subgroup H ρ
  · intro i j
    exact ⟨liftEntry H ρ i j, liftEntry_degree H ρ i j, fun _ => rfl⟩

end FiberFunctorProof

end

end OAI
