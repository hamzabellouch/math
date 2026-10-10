import OAI.Topology.CoarseAssembly.CirclePairing
import OAI.Topology.CoarseAssembly.RipsWindingTest

namespace OAI

/-! # The analytic winding test on a finite Rips component

This derives the finite-component index evaluation from the explicit
published scalar-circle pairing. The cocycle, continuous map, parametrized
loop and its degree are explicit.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable {X : Type} [Fintype X] {G : SimpleGraph X}

omit [Fintype X] in
theorem graphEdgeBound (hG : G.Connected) (r : ℕ) (hr : 1 ≤ r) :
    letI := graphMetric G hG
    ∀ x y, G.Adj x y → dist x y ≤ (r : ℝ) := by
  let := graphMetric G hG
  intro x y h
  rw [graphMetric_eq G hG]
  change (G.dist x y : ℝ) ≤ r
  exact_mod_cast (G.dist_le h.toWalk).trans (by simpa using hr)

/-- The analytic class of the parametrized boundary loop at this scale. -/
def graphLoopClass (input : PublishedCircleInput) (hG : G.Connected)
    (r : ℕ) (hr : 1 ≤ r) {x : X} (p : G.Walk x x) :
    letI := graphMetric G hG
    LocallyFiniteK1 (Point X (r : ℝ)) := by
  let := graphMetric G hG
  exact pushforward (compactMap (loopCircle (walkPath (by positivity)
    (graphEdgeBound hG r hr) p))) input.fundamental

/-- The finite-component analytic index is the original graph winding. -/
theorem graph_loop_index (input : PublishedCircleInput) (hG : G.Connected)
    (a : X → X → ℤ) (ha : ∀ x y, G.Adj x y → a y x = -a x y)
    (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x : X} (p : G.Walk x x) :
    letI := graphMetric G hG
    input.pairing (graphRipsCocycle hG a ha r hloop).toContinuousMap
      (graphLoopClass input hG r hr p) = walkCharge a p := by
  let := graphMetric G hG
  let c := graphRipsCocycle hG a ha r hloop
  change input.pairing c.toContinuousMap
    (pushforward (compactMap (loopCircle (walkPath (by positivity)
      (graphEdgeBound hG r hr) p))) input.fundamental) = _
  rw [input.loop_pairing c.toContinuousMap _ _
    (c.walkLift (by positivity) (graphEdgeBound hG r hr) p)]
  exact graphRipsCocycle_on_walk hG a ha r hr hloop p

/-- A charge-one boundary class has infinite order at the specified Rips
scale. Only the cited published circle-index input is conditional. -/
theorem graph_loop_infinite_order (input : PublishedCircleInput) (hG : G.Connected)
    (a : X → X → ℤ) (ha : ∀ x y, G.Adj x y → a y x = -a x y)
    (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x : X} (p : G.Walk x x) (hp : walkCharge a p = 1)
    (n : ℤ) (hn : n ≠ 0) :
    letI := graphMetric G hG
    n • graphLoopClass input hG r hr p ≠ 0 := by
  let := graphMetric G hG
  intro h
  have hi := graph_loop_index input hG a ha r hr hloop p
  have h' := congrArg (input.pairing (graphRipsCocycle hG a ha r hloop).toContinuousMap) h
  exact hn (by simpa [map_zsmul, hi, hp] using h')

end CoarseAssembly

end

end OAI
