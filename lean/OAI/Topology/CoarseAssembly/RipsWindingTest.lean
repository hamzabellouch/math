import OAI.Topology.CoarseAssembly.CocyclePathLifting
import OAI.Topology.CoarseAssembly.FiniteRips
import OAI.Topology.CoarseAssembly.GraphMetric

namespace OAI

/-! # Winding tests from the short-loop theorem

This connects the proved graph-theoretic small-loop argument to the actual
continuous circle map and its real path lift. It assumes no analytic pairing
or nonvanishing conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Rips

variable {X : Type*} {G : SimpleGraph X}

def graphRipsCocycle (hG : G.Connected) (a : X → X → ℤ)
    (ha : ∀ x y, G.Adj x y → a y x = -a x y) (r : ℕ)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0) :
    letI := graphMetric G hG
    IntegralCocycle X (r : ℝ) := by
  let := graphMetric G hG
  have hloop₂ : ∀ x (p : G.Walk x x), p.length ≤ 2 * r → walkCharge a p = 0 := by
    intro x p hp
    exact hloop x p (by omega)
  have toBound : ∀ x y : X, dist x y ≤ (r : ℝ) → G.dist x y ≤ r := by
    intro x y h
    change @dist X (graphMetric G hG).toDist x y ≤ (r : ℝ) at h
    rw [graphMetric_eq G hG] at h
    change (G.dist x y : ℝ) ≤ r at h
    exact_mod_cast h
  exact
    { charge := ripsCharge hG a
      antisymm := fun x y hxy => ripsCharge_antisymm hG a ha r hloop₂
        (toBound x y hxy)
      triangle := fun x y z hxy hyz hzx => ripsCharge_triangle hG a r hloop
        (toBound x y hxy) (toBound y z hyz) (toBound z x hzx) }

theorem graphRipsCocycle_on_walk (hG : G.Connected) (a : X → X → ℤ)
    (ha : ∀ x y, G.Adj x y → a y x = -a x y) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x y : X} (p : G.Walk x y) :
    letI := graphMetric G hG
    walkCharge (graphRipsCocycle hG a ha r hloop).charge p = walkCharge a p := by
  let := graphMetric G hG
  exact ripsCharge_on_walk hG a ha r hr (fun x p hp => hloop x p (by omega)) p

/-- The winding test on a finite Rips component has a real lift with the
same endpoint as the original graph charge. -/
theorem graph_winding_lift [Fintype X] (hG : G.Connected) (a : X → X → ℤ)
    (ha : ∀ x y, G.Adj x y → a y x = -a x y) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x : X} (p : G.Walk x x) :
    letI := graphMetric G hG
    let c := graphRipsCocycle hG a ha r hloop
    ∃ γ : Path (vertex x (by positivity : (0 : ℝ) ≤ r))
        (vertex x (by positivity : (0 : ℝ) ≤ r)),
      ∃ L : Path (0 : ℝ) (walkCharge a p : ℝ),
        ∀ t, c.circleMap (γ t) = (L t : AddCircle (1 : ℝ)) := by
  let := graphMetric G hG
  let c := graphRipsCocycle hG a ha r hloop
  have hE : ∀ x y, G.Adj x y → dist x y ≤ (r : ℝ) := by
    intro x y h
    change @dist X (graphMetric G hG).toDist x y ≤ (r : ℝ)
    rw [graphMetric_eq G hG]
    change (G.dist x y : ℝ) ≤ r
    exact_mod_cast (G.dist_le h.toWalk).trans (by simpa using hr)
  have hcharge : walkCharge c.charge p = walkCharge a p :=
    graphRipsCocycle_on_walk hG a ha r hr hloop p
  obtain ⟨L, hL⟩ := c.closed_walk_lift (by positivity) hE p
  refine ⟨walkPath (by positivity) hE p, L.cast rfl (by rw [hcharge]), ?_⟩
  exact hL

end CoarseAssembly

end

end OAI
