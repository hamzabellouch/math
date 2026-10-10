import Mathlib

namespace OAI

/-! Orthogonality of weighted path insertions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I P Q : Type} [Fintype I] [Fintype P] [Fintype Q]

omit [Fintype P] in
/-- Rows obtained by inserting disjoint labeled detours are orthogonal. -/
theorem insertion_matrix_mul_conjTranspose (f : I × P → Q)
    (hf : Function.Injective f) (a : I → ℂ) :
    let C : Matrix P Q ℂ := fun p q => ∑ i, if q=f (i,p) then a i else 0
    C*C.conjTranspose = (∑ i, a i*star (a i)) • (1 : Matrix P P ℂ) := by
  ext p r
  change (∑ q : Q, (∑ i : I, if q=f (i,p) then a i else 0) *
    star (∑ j : I, if q=f (j,r) then a j else 0)) =
      (∑ i : I, a i*star (a i)) * (if p=r then 1 else 0)
  simp only [star_sum,apply_ite star,star_zero,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ i : I, ∑ j : I, if f (i,r)=f (j,p) then a j*star (a i) else 0
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_mul,zero_mul,mul_ite,mul_zero]
    simp
  · have he : ∀ i j : I, f (i,r)=f (j,p) ↔ i=j ∧ p=r := by
      intro i j
      constructor
      · intro h
        obtain ⟨hi,hr⟩ := Prod.mk.inj (hf h)
        exact ⟨hi,hr.symm⟩
      · rintro ⟨rfl,rfl⟩
        rfl
    simp only [he]
    by_cases hpr : p=r
    · subst r
      simp
    · simp [hpr]

end HarmonicArtin.ParabolicIntersections

end OAI
