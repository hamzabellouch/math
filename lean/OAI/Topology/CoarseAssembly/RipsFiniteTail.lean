import OAI.Topology.CoarseAssembly.FiniteTailIndependence
import OAI.Topology.CoarseAssembly.ControlledRipsCycles
import OAI.Topology.CoarseAssembly.CountableHilbertSum

namespace OAI

/-! # Finite-tail invariance for the analytic Rips boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

abbrev scalarHilbert : HilbertSpace where
  Carrier := ℂ
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

local instance : SecondCountableTopology (lp (fun _ : ℕ => ℂ) 2) :=
  hilbertSum_secondCountable (fun _ => scalarHilbert)

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

theorem ControlledCycleFamily.boundary_eq_of_tail
    (c : ControlledCycleFamily Q r) (d : ControlledCycleFamily Q s)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s) (J : Finset ℕ)
    (htail : ∀ i, i ∉ J →
      ampleRipsOperator r (c.cycle i) (c.unital i) = ampleRipsOperator s (d.cycle i) (d.unital i)) :
    c.boundary o hr = d.boundary o hs := by
  let := separatedMetric o
  exact separatedFamilyBoundary_eq_of_tail o
    (fun i => ampleRipsOperator r (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator s (d.cycle i) (d.unital i))
    (c.bound + 4) (d.bound + 4) (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (by linarith [c.norm_le i]))
    (fun i => (ampleRipsOperator_norm_le s (d.cycle i) (d.unital i)).trans
      (by linarith [d.norm_le i]))
    (r + r) (s + s) (add_nonneg hr hr) (add_nonneg hs hs)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation s hs (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint s (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact s (d.cycle i) (d.unital i) (d.selfAdjoint i))
    J htail

end CoarseAssembly.Rips

end

end OAI
