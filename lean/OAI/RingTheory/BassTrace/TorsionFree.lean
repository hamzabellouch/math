import OAI.RingTheory.BassTrace.TraceRank
import OAI.RingTheory.BassTrace.RegularRepresentation
import OAI.RingTheory.BassTrace.CoefficientDescent

namespace OAI

/-! Idempotent and trace consequences for torsion-free groups. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

/-- The scalar specialization of the identity-support trace formula. -/
lemma scalar_trace_eq_augmentation (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : canonicalTrace e = augmentation e := by
  let b : Matrix (Fin 1) (Fin 1) (MonoidAlgebra ℂ G) := fun _ _ => e
  have hb : b * b = b := by
    apply Matrix.ext
    intro i j
    change (∑ _ : Fin 1, e * e) = e
    simpa using he
  simpa [matrixTrace, Matrix.trace, Matrix.diag, b] using matrix_trace_eq_augmentation hG b hb

/-- Kaplansky's scalar idempotent assertion over the complex numbers. -/
theorem complex_idempotent (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have ht : e.coeff 1 = augmentation e := scalar_trace_eq_augmentation hG e he
  have haug : augmentation e * (augmentation e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  rcases mul_eq_zero.mp haug with hz | ho
  · exact Or.inl (Regular.idempotent_eq_zero_of_coeff_one_eq_zero e he (ht.trans hz))
  · have ht' : e.coeff 1 = 1 := ht.trans (sub_eq_zero.mp ho)
    have hc : (1 - e) * (1 - e) = 1 - e := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, he]
      abel
    have hz : (1 - e).coeff 1 = 0 := by simp [ht']
    exact Or.inr (sub_eq_zero.mp
      (Regular.idempotent_eq_zero_of_coeff_one_eq_zero (1 - e) hc hz)).symm

/-- Kaplansky's assertion over any commutative characteristic-zero domain. -/
theorem domain_idempotent (hG : TorsionFree G)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1 :=
  descend_idempotents (complex_idempotent hG) R e he

/-- Trace/rank, equality and range on algebraic K₀, and characteristic-zero
scalar idempotents for torsion-free groups. -/
theorem torsion_free_corollary (G : Type*) [Group G] (hG : TorsionFree G) :
    ((∀ (q : ℕ), 1 ≤ q →
      ∀ e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G), e ^ 2 = e →
        matrixTrace e = ((augmentedMatrix e).rank : ℂ)) ∧
      traceK0 (G := G) = (Int.castAddHom ℂ).comp augmentationRank ∧
      Set.range (traceK0 (G := G)) = Set.range (fun z : ℤ => (z : ℂ))) ∧
    (∀ (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
      (e : MonoidAlgebra R G), e ^ 2 = e → e = 0 ∨ e = 1) := by
  refine ⟨⟨?_, traceK0_eq_augmentationRank hG, traceK0_range hG⟩, ?_⟩
  · intro q _ e he
    exact matrix_trace_eq_rank hG e (by simpa only [pow_two] using he)
  · intro R _ _ _ e he
    exact domain_idempotent hG R e (by simpa only [pow_two] using he)

end TorsionFreeBass
end

end OAI
