import OAI.Topology.CoarseAssembly.AmpleRipsFamily

namespace OAI

/-! # Increasing-scale compatibility of the explicit Rips representatives

The barycentric coordinate functions pull back identically under increasing
the Rips scale. Consequently the localized operators themselves agree,
before taking a K-theory class.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X]
  {r s : ℝ} (hrs : r ≤ s)

def scaleFunctionHom : C(Point X s, ℂ) →⋆ₐ[ℂ] C(Point X r, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨coarsen hrs, (coarsen_closedEmbedding hrs).continuous⟩

omit [Fintype X] in
theorem scaleFunctionHom_sqrt (x : X) :
    scaleFunctionHom hrs (sqrtCoordinate s x) = sqrtCoordinate r x := rfl

def coarsenedCycle (c : OddCycle C(Point X r, ℂ)) : OddCycle C(Point X s, ℂ) :=
  c.precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom

theorem coarsenedCycle_unital (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) : (coarsenedCycle hrs c).representation 1 = 1 := by
  change c.representation (scaleFunctionHom hrs 1) = 1
  rw [map_one, hπ]

theorem coarsenedCycle_representedSqrt (c : OddCycle C(Point X r, ℂ)) :
    representedSqrt s (coarsenedCycle hrs c) = representedSqrt r c := rfl

variable [DecidableEq X]

theorem ripsSpatialOperator_scale (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    (show Operator X c.space from
      ripsSpatialOperator s (coarsenedCycle hrs c) (coarsenedCycle_unital hrs c hπ)) =
      ripsSpatialOperator r c hπ := rfl

theorem ampleRipsOperator_scale (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) :
    ampleRipsOperator s (coarsenedCycle hrs c) (coarsenedCycle_unital hrs c hπ) =
      ampleRipsOperator r c hπ := rfl

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem ampleRipsFamilyBoundary_scale (o : ∀ i, V i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ i, ‖(c i).operator‖ ≤ C) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o s hs (fun i => coarsenedCycle hrs (c i))
      (fun i => coarsenedCycle_unital hrs (c i) (hπ i)) hF C hC hnorm =
      ampleRipsFamilyBoundary o r hr c hπ hF C hC hnorm := rfl

end CoarseAssembly.Rips

end

end OAI
