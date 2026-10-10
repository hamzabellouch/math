import OAI.Topology.CoarseAssembly.ControlledRipsCycles
import OAI.Topology.CoarseAssembly.SeparatedFamilyNearby

namespace OAI

/-! # Norm comparison of bounded cycle families in the actual Roe boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

theorem ControlledCycleFamily.boundary_eq_of_ample_nearby
    (c d : ControlledCycleFamily Q r) (o : ∀ i, Q i) (hr : 0 ≤ r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : δ < 1 / 4)
    (hnear : ∀ i, ‖ampleRipsOperator r (d.cycle i) (d.unital i) -
      ampleRipsOperator r (c.cycle i) (c.unital i)‖ ≤ δ) :
    c.boundary o hr = d.boundary o hr := by
  let := separatedMetric o
  exact separatedFamilyBoundary_eq_of_nearby o _ _ (c.bound + 4) (d.bound + 4)
    (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (add_le_add (c.norm_le i) le_rfl))
    (fun i => (ampleRipsOperator_norm_le r (d.cycle i) (d.unital i)).trans
      (add_le_add (d.norm_le i) le_rfl))
    (r + r) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation r hr (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    δ hδ hsmall hnear

end CoarseAssembly.Rips

end

end OAI
