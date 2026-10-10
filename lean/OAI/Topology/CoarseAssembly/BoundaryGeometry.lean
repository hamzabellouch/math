import OAI.Topology.CoarseAssembly.BoundaryEmbedding
import OAI.Topology.CoarseAssembly.FilledWalks
import OAI.Topology.CoarseAssembly.RipsProperEmbedding
import OAI.Topology.CoarseAssembly.RoeInclusion

namespace OAI

/-! # The concrete proper boundary inclusions

The boundary is the depth-zero vertex subset with the induced metric from
the total graph family. Its projection to the base is nonexpanding. These
are the actual two vertex inclusions used for assembly naturality.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic DiscreteRoe

private theorem walk_image_dist_le {V Z : Type*} (G : SimpleGraph V)
    [PseudoMetricSpace Z] (f : V → Z)
    (hedge : ∀ x y, G.Adj x y → dist (f x) (f y) ≤ 1)
    {x y : V} (p : G.Walk x y) : dist (f x) (f y) ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    calc
      dist (f x) (f z) ≤ dist (f x) (f y) + dist (f y) (f z) := dist_triangle _ _ _
      _ ≤ 1 + (p.length : ℝ) := add_le_add (hedge x y h) ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℝ) := by simp; ring

theorem fiberProjection_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (j : ℕ) (x y : FiberVertex j) :
    dist x.1 y.1 ≤ @dist _ (componentMetric S t j).toDist x y := by
  obtain ⟨p, hp⟩ := (fiberedGraph_connected S t j).exists_walk_length_eq_dist x y
  rw [componentMetric_eq]
  change dist x.1 y.1 ≤ ((fiberedGraph S t j).dist x y : ℝ)
  rw [← hp]
  apply walk_image_dist_le (fiberedGraph S t j) (fun z => z.1)
  intro u v h
  obtain ⟨s, hs, hp, _⟩ := h.2
  rcases hp with hsame | ⟨hadj, _⟩
  · simp [hsame]
  · exact discEdgeBound u.1 v.1 hadj

theorem vertexProjection_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : VertexUnion) :
    dist x.1 y.1 ≤ @dist _ (vertexUnionMetric S t).toDist x y := by
  let := componentMetric S t
  rcases x with ⟨⟨i, u⟩, q⟩
  rcases y with ⟨⟨j, v⟩, z⟩
  change separatedDist discBoundaryBase ⟨i, u⟩ ⟨j, v⟩ ≤
    separatedDist fiberBoundaryBase ⟨i, ⟨u, q⟩⟩ ⟨j, ⟨v, z⟩⟩
  by_cases hij : i = j
  · subst j
    simp only [separatedDist_same]
    exact fiberProjection_nonexpanding S t i ⟨u, q⟩ ⟨v, z⟩
  · rw [separatedDist_different discBoundaryBase hij,
      separatedDist_different fiberBoundaryBase hij]
    exact add_le_add
      (add_le_add (fiberProjection_nonexpanding S t i ⟨u, q⟩ (fiberBoundaryBase i)) le_rfl)
      (fiberProjection_nonexpanding S t j (fiberBoundaryBase j) ⟨v, z⟩)

@[instance_reducible] def boundaryMetric (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    MetricSpace BoundaryVertex := by
  exact MetricSpace.induced boundaryToVertex boundaryToVertex.injective (vertexUnionMetric S t)

theorem boundaryToVertex_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    ∀ x y, @dist VertexUnion (vertexUnionMetric S t).toDist
      (boundaryToVertex x) (boundaryToVertex y) ≤
      @dist BoundaryVertex (boundaryMetric S t).toDist x y :=
  fun _ _ => le_rfl

theorem boundaryToBase_nonexpanding (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    ∀ x y, dist (boundaryToBase x) (boundaryToBase y) ≤
      @dist BoundaryVertex (boundaryMetric S t).toDist x y :=
  fun x y => vertexProjection_nonexpanding S t (boundaryToVertex x) (boundaryToVertex y)

end CoarseAssembly

end

end OAI
