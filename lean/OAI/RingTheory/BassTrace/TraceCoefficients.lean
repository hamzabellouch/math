import Mathlib

namespace OAI

namespace BassTrace

open scoped Classical

noncomputable def classCoefficient {G : Type*} [Group G]
    (g : G) (a : MonoidAlgebra ℂ G) : ℂ := by
  classical
  exact a.coeff.sum fun h z => if IsConj h g then z else 0

noncomputable def idempotentTraceCoefficient {G : Type*} [Group G]
    {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (g : G) : ℂ :=
  classCoefficient g (Matrix.trace e)

variable {G : Type*} [Group G]

@[simp] theorem classCoefficient_zero (g : G) :
    classCoefficient g 0 = 0 := by
  simp [classCoefficient]

@[simp] theorem classCoefficient_single (g h : G) (z : ℂ) :
    classCoefficient g (MonoidAlgebra.single h z) = if IsConj h g then z else 0 := by
  classical
  simp [classCoefficient, Finsupp.sum_single_index]

@[simp] theorem classCoefficient_add (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a + b) = classCoefficient g a + classCoefficient g b := by
  classical
  apply Finsupp.sum_add_index
  · intro h _
    simp
  · intro h _ z w
    split_ifs <;> simp

@[simp] theorem classCoefficient_smul (g : G) (z : ℂ) (a : MonoidAlgebra ℂ G) :
    classCoefficient g (z • a) = z * classCoefficient g a := by
  classical
  unfold classCoefficient
  rw [MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (fun _ => by simp)]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp

@[simp] theorem classCoefficient_sum {ι : Type*} (g : G) (s : Finset ι)
    (f : ι → MonoidAlgebra ℂ G) :
    classCoefficient g (∑ i ∈ s, f i) = ∑ i ∈ s, classCoefficient g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem classCoefficient_mul_comm (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a * b) = classCoefficient g (b * a) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
      induction b using MonoidAlgebra.induction_on with
      | of k =>
          have hconj : IsConj (h * k) (k * h) := by
            apply isConj_iff.mpr
            exact ⟨k, by simp [mul_assoc]⟩
          have hiff : IsConj (h * k) g ↔ IsConj (k * h) g :=
            ⟨hconj.symm.trans, hconj.trans⟩
          change classCoefficient g (MonoidAlgebra.single h 1 * MonoidAlgebra.single k 1) =
            classCoefficient g (MonoidAlgebra.single k 1 * MonoidAlgebra.single h 1)
          simp only [MonoidAlgebra.single_mul_single, classCoefficient_single, hiff]
      | add b c hb hc => simp only [mul_add, add_mul, classCoefficient_add, hb, hc]
      | smul z b hb => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, hb]
  | add a c ha hc => simp only [add_mul, mul_add, classCoefficient_add, ha, hc]
  | smul z a ha => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, ha]

theorem classCoefficient_matrix_mul_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : G) (a : Matrix ι κ (MonoidAlgebra ℂ G))
    (b : Matrix κ ι (MonoidAlgebra ℂ G)) :
    classCoefficient g (Matrix.trace (a * b)) =
      classCoefficient g (Matrix.trace (b * a)) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, classCoefficient_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact classCoefficient_mul_comm g _ _

end BassTrace

end OAI
