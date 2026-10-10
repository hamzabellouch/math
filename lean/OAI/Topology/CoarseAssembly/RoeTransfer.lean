import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RoeCalculus

namespace OAI

/-!
# Norm-closure and spatial factorization for the finite-fiber transfer

The missing construction of the finite-propagation lift is isolated as an
explicit witness here; it is not treated as a published input. Once a lift
has been constructed by matchings, the following argument proves that the
spatial homomorphism lands in the actual reduced Roe algebra.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped Topology

variable {B D X H : Type*} [DecidableEq B] [DecidableEq D] [DecidableEq X]
variable [PseudoMetricSpace B] [PseudoMetricSpace D] [PseudoMetricSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [DecidableEq D] [DecidableEq X] [PseudoMetricSpace D] [PseudoMetricSpace X] in
theorem conjugation_continuous (V : Module D H →ₗᵢ[ℂ] Module X H) :
    Continuous (operatorConjugation V) := by
  show Continuous (fun T : Operator D H =>
    V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint))
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

/-- The range proof after constructing the matching lift of each generator. -/
theorem conjugation_mem_of_sandwich_lifts
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (V : Module D H →ₗᵢ[ℂ] Module X H)
    (P : Operator X H) (Pn : ℕ → Operator X H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds P))
    (hprop : ∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n))
    (hlift : ∀ T : Operator D H, Generator T →
      ∃ A : Operator X H, Generator A ∧ P * A * P = operatorConjugation V T)
    {T : Operator D H} (hT : T ∈ algebra (X := D) (H := H)) :
    operatorConjugation V T ∈ algebra (X := X) (H := H) := by
  apply map_mem (operatorConjugationHom V) (conjugation_continuous V) _ hT
  intro S hS
  obtain ⟨A, hA, heq⟩ := hlift S hS
  change operatorConjugation V S ∈ algebra (X := X) (H := H)
  rw [← heq]
  apply sandwich_mem hlim
  intro n
  obtain ⟨r, hr, hn⟩ := hprop n
  exact generator_sandwich finiteBalls hA hr hn

@[simp] theorem conjugationHom_apply
    (V : Module D H →ₗᵢ[ℂ] Module X H) (hV : MapsToRoe V)
    (T : algebra (X := D) (H := H)) :
    (conjugationHom V hV T : Operator X H) = operatorConjugation V T := rfl

theorem conjugationHom_injective
    (V : Module D H →ₗᵢ[ℂ] Module X H) (hV : MapsToRoe V) :
    Function.Injective (conjugationHom V hV) := by
  intro T S h
  apply Subtype.ext
  apply operatorConjugation_injective V
  exact congrArg Subtype.val h

/-- Exact operator factorization remains exact after restriction to Roe
algebras. This is the final operator identity `Ad V ∘ Ad E = Ad I`. -/
theorem conjugationHom_comp_apply
    (E : Module B H →ₗᵢ[ℂ] Module D H)
    (V : Module D H →ₗᵢ[ℂ] Module X H)
    (hE : MapsToRoe E) (hV : MapsToRoe V) (hVE : MapsToRoe (V.comp E))
    (T : algebra (X := B) (H := H)) :
    conjugationHom (D := D) (X := X) (H := H) V hV
      (conjugationHom (D := B) (X := D) (H := H) E hE T) =
      conjugationHom (D := B) (X := X) (H := H) (V.comp E) hVE T := by
  apply Subtype.ext
  exact operatorConjugation_comp V E T

end CoarseAssembly.DiscreteRoe

end

end OAI
