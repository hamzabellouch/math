import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FiniteWords
import OAI.Topology.CoarseAssembly.TranscendentalUnit

namespace OAI

/-!
# A single principal holonomy for all finite scales

The choice in §3 is made once. The separation level can then depend on the
length bound, without changing the chosen 2-adic unit.
-/

namespace CoarseAssembly.Congruence

theorem chosenHolonomyUnit_transcendental :
    Transcendental ℤ (chosenHolonomyUnit : ℤ_[2]) :=
  (exists_transcendental_principal_unit (p := 2)).choose_spec.1

theorem chosenHolonomyUnit_principal :
    ∃ a : ℤ_[2], (chosenHolonomyUnit : ℤ_[2]) = 1 + (2 : ℤ_[2]) * a :=
  (exists_transcendental_principal_unit (p := 2)).choose_spec.2

/-- The fixed principal holonomy excludes short charged closed lifts at every
finite length bound. This is an arithmetic statement, not a coarse assembly
or K-homology theorem. -/
theorem chosenHolonomy_short_lifts (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ z : Quotient k,
      ∀ steps : List (ArithmeticGroup × ℤ), steps.length ≤ A →
        (∀ s ∈ steps, s.1 ∈ S ∧ s.2.natAbs ≤ 1) →
        holonomyEndpoint (holonomy chosenHolonomyUnit k) (reduceSteps k steps) z = z →
        holonomyCharge steps = 0 :=
  bounded_closed_lifts_have_zero_charge chosenHolonomyUnit
    chosenHolonomyUnit_transcendental S A

end CoarseAssembly.Congruence

end OAI
