import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.GraphMetric
import OAI.Topology.CoarseAssembly.SeparatedGeometry
import OAI.Topology.CoarseAssembly.FiberDegree
import OAI.Topology.CoarseAssembly.FiberConnected
import Mathlib.Topology.MetricSpace.TransferInstance

namespace OAI

/-! # The actual base and fibered coarse unions

Both metrics restrict to shortest-path metrics on the components. The
fibered union is indexed by base vertices so its Hilbert module has exactly
the form used by the finite-fiber transfer theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

instance discGraphMetric (j : ℕ) : MetricSpace (Disc j) :=
  graphMetricOrDiscrete (discGraph j)

theorem discGraphMetric_eq (j : ℕ) :
    discGraphMetric j = connectedGraphMetric (discGraph j) (discGraph_connected j) :=
  graphMetricOrDiscrete_eq _ _

instance baseUnionMetric : MetricSpace BaseUnion := separatedMetric discBoundaryBase

theorem componentMetric_eq (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    componentMetric S t j = connectedGraphMetric (fiberedGraph S t j) (fiberedGraph_connected S t j) :=
  graphMetricOrDiscrete_eq _ _

theorem baseUnion_uniform_balls : UniformFiniteBalls BaseUnion := by
  classical
  apply separated_uniform_finite_balls discBoundaryBase
  intro R hR
  refine ⟨8 ^ ⌈R⌉₊, ?_⟩
  intro j u
  rw [discGraphMetric_eq]
  exact graphMetric_ball_bound (discGraph j) (discGraph_connected j) baseNeighbors 7
    (fun x y h => (mem_baseNeighbors x y).mpr (Or.inr h)) card_baseNeighbors_le R u

theorem baseUnion_separated (x y : BaseUnion) (h : x ≠ y) : 1 ≤ dist x y :=
  separated_uniform_discrete discBoundaryBase
    (fun j _x _y h => by
      rw [discGraphMetric_eq, ← graphMetric_eq]
      exact graphMetric_separated (discGraph j) (discGraph_connected j) h) x y h

theorem componentUnion_uniform_balls (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @UniformFiniteBalls ((j : ℕ) × FiberVertex j)
      (componentUnionMetric S t).toPseudoMetricSpace := by
  classical
  let := componentMetric S t
  apply separated_uniform_finite_balls fiberBoundaryBase
  intro R hR
  refine ⟨(7 * (symmetricMoves S).card * 2 ^ 9 + 1) ^ ⌈R⌉₊, ?_⟩
  intro j x
  change ∃ b : Finset (FiberVertex j),
    (∀ y, y ∈ b ↔ @dist _ (componentMetric S t j).toDist x y ≤ R) ∧ _
  rw [componentMetric_eq]
  exact graphMetric_ball_bound (fiberedGraph S t j) (fiberedGraph_connected S t j)
    (fiberedNeighbors S t) _
    (fun x y h => (mem_fiberedNeighbors S t x y).mpr h)
    (card_fiberedNeighbors_le S t) R x

/-- Transport an exact finite-ball bound across an isometric equivalence. -/
theorem uniform_balls_of_equiv {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ Y) (he : ∀ x y, dist (e x) (e y) = dist x y)
    (hY : UniformFiniteBalls Y) : UniformFiniteBalls X := by
  classical
  intro R hR
  obtain ⟨N, hN⟩ := hY R hR
  refine ⟨N, ?_⟩
  intro x
  obtain ⟨b, hb, hcard⟩ := hN (e x)
  refine ⟨b.map e.symm.toEmbedding, ?_, ?_⟩
  · intro y
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, hb, he]
  · simpa only [Finset.card_map] using hcard

theorem vertexUnion_uniform_balls (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @UniformFiniteBalls VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace := by
  let := componentUnionMetric S t
  let := vertexUnionMetric S t
  apply uniform_balls_of_equiv (Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u)))
    (fun _ _ => rfl)
  exact componentUnion_uniform_balls S t

theorem vertexUnion_separated (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : VertexUnion) (h : x ≠ y) :
    1 ≤ @dist VertexUnion (vertexUnionMetric S t).toDist x y := by
  let := componentMetric S t
  let e := Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u))
  exact separated_uniform_discrete fiberBoundaryBase
    (fun j _x _y h => by
      change 1 ≤ @dist _ (componentMetric S t j).toDist _x _y
      rw [componentMetric_eq, ← graphMetric_eq]
      exact graphMetric_separated (fiberedGraph S t j)
        (fiberedGraph_connected S t j) h) (e x) (e y) (fun he => h (e.injective he))

end CoarseAssembly

end

end OAI
