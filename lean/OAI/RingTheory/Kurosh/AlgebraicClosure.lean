import Mathlib
import OAI.RingTheory.Kurosh.LimitEvaluation

namespace OAI

/-! Algebraicity, inverse closure, and countability of generated algebras. -/

namespace KuroshConstruction

open Filter

section AlgebraicSubalgebra

variable (U : Ultrafilter ℕ) [hU : Fact ((U : Filter ℕ) ≤ atTop)]
  (K A : ℕ → Type*) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
  [∀ i, Algebra (K i) (A i)]
  (f : ∀ i j, i ≤ j → K i →+* K j)
  [DirectedSystem K (fun i j h => f i j h)]
  {I : Type*} (X : I → ∀ i, A i)

def RelationsScheduled : Prop :=
  ∀ j (p : FreeAlgebra (K j) I), ∃ m, ∃ q : Polynomial (K m),
    q.Monic ∧ ∀ᶠ i in atTop,
      tailPolynomialValue K A f m q (tailFreeValue K A f X j p) i = 0

theorem scheduled_isIntegral (hs : RelationsScheduled K A f X)
    (r : DivisionUltraproduct U A)
    (hr : r ∈ Algebra.adjoin (DirectLimit K f) (Set.range (fun c => ultraMap U A (X c)))) :
    IsIntegral (DirectLimit K f) r := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift] at hr
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨j, p, rfl⟩ := freePolynomial_finite_stage K f p
  obtain ⟨m, q, hq, he⟩ := hs j p
  refine ⟨q.map (DirectLimit.Ring.of K f m), hq.map _, ?_⟩
  change Polynomial.aeval (R := DirectLimit K f)
    (FreeAlgebra.lift (DirectLimit K f) (fun c => ultraMap U A (X c))
      (freeScalarChange (DirectLimit.Ring.of K f j) p)) _ = 0
  rw [ultraFree_evaluate]
  change Polynomial.aeval (R := DirectLimit K f)
    (ultraMap U A (tailFreeValue K A f X j p)) _ = 0
  rw [ultraPolynomial_evaluate, ← map_zero (ultraMap U A)]
  exact (ultraMap_eq_iff U A _ _).mpr (he.filter_mono hU.out)

@[instance_reducible] noncomputable def scheduledDivisionRing (hs : RelationsScheduled K A f X) :
    DivisionRing (Algebra.adjoin (DirectLimit K f) (Set.range (fun c => ultraMap U A (X c)))) :=
  DivisionRing.ofIsUnitOrEqZero (fun r => by
    classical
    by_cases hr : r = 0
    · exact Or.inr hr
    · exact Or.inl (((isIntegral_algHom_iff
        (Algebra.adjoin (DirectLimit K f) (Set.range (fun c => ultraMap U A (X c)))).val
        Subtype.val_injective).mp (scheduled_isIntegral U K A f X hs r r.property)).isUnit hr))

end AlgebraicSubalgebra

section Countability

variable (K D I : Type*) [Field K] [DivisionRing D] [Algebra K D]
  [Countable K] [Countable I] (X : I → D)

theorem countable_generated_algebra : Countable (Algebra.adjoin K (Set.range X)) := by
  have : Countable (FreeMonoid I) := inferInstanceAs (Countable (List I))
  have : Countable (MonoidAlgebra K (FreeMonoid I)) :=
    Function.Injective.countable MonoidAlgebra.coeffEquiv.injective
  have : Countable (FreeAlgebra K I) :=
    Function.Injective.countable (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := I)).injective
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  exact Function.Surjective.countable (FreeAlgebra.lift K X).rangeRestrict_surjective

end Countability

end KuroshConstruction

end OAI
