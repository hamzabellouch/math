import OAI.Topology.CoarseAssembly.CocycleCircleMap
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Compact subsets of a locally finite Rips complex

A compact set of probability weights has its entire support in one finite
vertex set. The proof uses a finite cover by positive-coordinate stars and
the finite metric balls around those coordinates.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

theorem compact_support_finite
    (hballs : ∀ x : X, Set.Finite {y : X | dist x y ≤ r})
    {K : Set (Point X r)} (hK : IsCompact K) :
    ∃ s : Finset X, ∀ p ∈ K, p.weight.support ⊆ s := by
  classical
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover
    (fun x : X => {p : Point X r | 0 < p.weight x})
    (fun x => isOpen_lt continuous_const (coordinate_continuous x)) (by
      intro p _
      obtain ⟨x, hx⟩ := p.exists_positive
      exact Set.mem_iUnion.mpr ⟨x, hx⟩)
  let s : Finset X := a.biUnion (fun x => (hballs x).toFinset)
  refine ⟨s, ?_⟩
  intro p hp y hy
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (ha hp)
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  exact (hballs x).mem_toFinset.mpr
    (p.diameter x (Finsupp.mem_support_iff.mpr (ne_of_gt hpx)) y hy)

end CoarseAssembly.Rips

end

end OAI
