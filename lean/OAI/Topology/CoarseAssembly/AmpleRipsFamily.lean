import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsLocalization
import OAI.Topology.CoarseAssembly.SeparableEmbedding
import OAI.Topology.CoarseAssembly.CoefficientIsometry
import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary

namespace OAI

/-! # Spatial representatives for finite-Rips families on the fixed ample module

The source Hilbert spaces may vary with the component. Each is embedded
isometrically into ℓ²(ℕ, ℂ), and the operator is extended by the identity.
The compact square defects give one whole-union boundary class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ampleRipsOperator_norm_le (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : ‖ampleRipsOperator r c hπ‖ ≤ ‖c.operator‖ + 4 := by
  exact (coefficientExtension_norm_le _ _).trans
    (by linarith [ripsSpatialOperator_norm_le r c hπ])

theorem ampleRipsOperator_selfAdjoint (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (ampleRipsOperator r c hπ) :=
  coefficientExtension_selfAdjoint _ _ (ripsSpatialOperator_selfAdjoint r c hπ hF)

theorem ampleRipsOperator_propagation (r : ℝ) (hr : 0 ≤ r)
    (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    PropagationLE (r + r) (ampleRipsOperator r c hπ) :=
  coefficientExtension_propagation _ (add_nonneg hr hr) (ripsSpatialOperator_propagation r hr c hπ)

theorem ampleRipsOperator_square_compact (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsCompactOperator (ampleRipsOperator r c hπ * ampleRipsOperator r c hπ -
      (1 : Operator X (lp (fun _ : ℕ => ℂ) 2))) :=
  coefficientExtension_square_compact _ _ (ripsSpatialOperator_square_compact r c hπ hF)

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

end CoarseAssembly.Rips

end

end OAI
