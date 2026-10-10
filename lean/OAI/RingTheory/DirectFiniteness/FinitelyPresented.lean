import Mathlib
import OAI.RingTheory.DirectFiniteness.PrescribedPresentation
import OAI.RingTheory.DirectFiniteness.OddTorsion
import OAI.RingTheory.DirectFiniteness.Main

namespace OAI

/-! The prescribed finitely presented counterexample in characteristic two. -/

namespace KaplanskyCounterexample

open Prescription

theorem thm_main :
    (∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1) ∧
    (2 ≤ selectedH ∧ selectedH ≤ 217 ∧ Test selectedInput selectedPair ∧
      (∀ h, Succeeds h → selectedH ≤ h) ∧
      (∀ p, Test selectedInput p →
        @LE.le _ (pairOrder selectedInput).toLE selectedPair p)) ∧
    Group.IsFinitelyPresented Output.G ∧
    (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : Output.G), orderOf g = ℓ) ∧
    Output.a * Output.b = 1 ∧ Output.b * Output.a ≠ 1 := by
  refine ⟨?_, finite_search_terminates, Output.prescribed_finitelyPresented,
    Output.prescribed_odd_prime_order, Output.prescribed_products⟩
  exact ⟨Output.Coeff, inferInstance, inferInstance, inferInstance,
    Output.G, inferInstance, Output.prescribed_finitelyPresented,
    Output.prescribed_odd_prime_order, Output.a, Output.b, Output.prescribed_products⟩


/-- The existential main result of the characteristic-two paper, separated from
the certificates for its prescribed construction. -/
theorem finitelyPresented_counterexample :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1 :=
  thm_main.1

end KaplanskyCounterexample

end OAI
