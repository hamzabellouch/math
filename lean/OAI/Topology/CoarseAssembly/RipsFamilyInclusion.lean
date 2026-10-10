import OAI.Topology.CoarseAssembly.SeparatedFamilyInclusion
import OAI.Topology.CoarseAssembly.CoefficientInclusion
import OAI.Topology.CoarseAssembly.ControlledRipsCycles

namespace OAI

/-! # Naturality of the controlled Rips boundary under component inclusions -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] {r : ℝ}

def ControlledCycleFamily.included (c : ControlledCycleFamily Q r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y) :
    ControlledCycleFamily P r where
  cycle i := includedCycle r (e i) (hei i) (c.cycle i)
  unital i := includedCycle_unital r (e i) (hei i) (c.cycle i) (c.unital i)
  selfAdjoint := c.selfAdjoint
  bound := c.bound
  bound_nonneg := c.bound_nonneg
  norm_le := c.norm_le

theorem ControlledCycleFamily.boundary_included (c : ControlledCycleFamily Q r)
    (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y) :
    letI := separatedMetric o
    letI := separatedMetric p
    OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he) (c.boundary o hr) =
      (c.included e hei).boundary p hr := by
  let := separatedMetric o
  let := separatedMetric p
  let d := c.included e hei
  exact separatedFamilyBoundary_inclusion o p e he
    (fun i => ampleRipsOperator r (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator r (d.cycle i) (d.unital i))
    (c.bound + 4) (d.bound + 4) (by linarith [c.bound_nonneg]) (by linarith [d.bound_nonneg])
    (fun i => (ampleRipsOperator_norm_le r (c.cycle i) (c.unital i)).trans
      (by linarith [c.norm_le i]))
    (fun i => (ampleRipsOperator_norm_le r (d.cycle i) (d.unital i)).trans
      (by linarith [d.norm_le i]))
    (r + r) (r + r) (add_nonneg hr hr) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c.cycle i) (c.unital i))
    (fun i => ampleRipsOperator_propagation r hr (d.cycle i) (d.unital i))
    (fun i => ampleRipsOperator_selfAdjoint r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_selfAdjoint r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (c.cycle i) (c.unital i) (c.selfAdjoint i))
    (fun i => ampleRipsOperator_square_compact r (d.cycle i) (d.unital i) (d.selfAdjoint i))
    (fun i => ampleRipsOperator_inclusion r (e i) (hei i) (c.cycle i) (c.unital i))

end CoarseAssembly.Rips

end

end OAI
