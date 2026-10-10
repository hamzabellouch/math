import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.BoundedGeometry
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # The metric of a connected graph

The metric on a connected graph is exactly the real-valued shortest-path
length. A proof-independent extension uses the discrete metric otherwise.
-/

noncomputable section

namespace CoarseAssembly

variable {V : Type*} (G : SimpleGraph V)

theorem graphMetricOrDiscrete_eq (hG : G.Connected) :
    graphMetricOrDiscrete G = connectedGraphMetric G hG := by
  classical
  simp only [graphMetricOrDiscrete, dite_eq_left hG]

@[instance_reducible] def graphMetric (_hG : G.Connected) : MetricSpace V :=
  graphMetricOrDiscrete G

theorem graphMetric_eq (hG : G.Connected) :
    graphMetric G hG = connectedGraphMetric G hG :=
  graphMetricOrDiscrete_eq G hG

theorem graphMetric_separated (hG : G.Connected) {x y : V} (hxy : x ≠ y) :
    (1 : ℝ) ≤ @dist V (graphMetric G hG).toDist x y := by
  rw [graphMetric_eq]
  change (1 : ℝ) ≤ (G.dist x y : ℝ)
  exact_mod_cast hG.pos_dist_of_ne hxy

/-- An exact metric ball, with the explicit bound inherited from degree. -/
theorem graphMetric_ball_bound [DecidableEq V] (hG : G.Connected)
    (neighbors : V → Finset V) (d : ℕ)
    (hN : ∀ x y, G.Adj x y → y ∈ neighbors x)
    (hd : ∀ x, (neighbors x).card ≤ d) (R : ℝ) (x : V) :
    ∃ b : Finset V,
      (∀ y, y ∈ b ↔ (G.dist x y : ℝ) ≤ R) ∧ b.card ≤ (d + 1) ^ ⌈R⌉₊ := by
  classical
  let b := (walkBall neighbors x ⌈R⌉₊).filter (fun y => (G.dist x y : ℝ) ≤ R)
  refine ⟨b, ?_, ?_⟩
  · intro y
    simp only [b, Finset.mem_filter]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
    have hlen : p.length ≤ ⌈R⌉₊ := by
      rw [hp]
      exact_mod_cast hy.trans (Nat.le_ceil R)
    exact walkBall_mono neighbors x hlen (endpoint_mem_walkBall neighbors hN p)
  · exact (Finset.card_filter_le _ _).trans (card_walkBall_le neighbors d hd x ⌈R⌉₊)

end CoarseAssembly

end

end OAI
