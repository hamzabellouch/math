import OAI.Topology.CoarseAssembly.BoundaryWalks
import OAI.Topology.CoarseAssembly.RipsFamilyMap

namespace OAI

/-! # Compact boundary components in the actual boundary metric

The disjoint family of finite boundary vertex sets is isometric to the
depth-zero subtype used for the spatial boundary maps.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips

@[instance_reducible] def boundaryComponentMetric (S : Finset ArithmeticGroup)
    (t : ℤ_[2]ˣ) (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  MetricSpace.induced (boundaryFiberEmbedding j) (boundaryFiberEmbedding j).injective
    (componentMetric S t j)

@[instance_reducible] def boundaryComponentsMetric (S : Finset ArithmeticGroup)
    (t : ℤ_[2]ˣ) : MetricSpace (Sigma BoundaryComponent) := by
  letI := boundaryComponentMetric S t
  exact separatedMetric boundaryRoot

def boundaryReindex : Sigma BoundaryComponent ≃ BoundaryVertex where
  toFun b := ⟨⟨b.1, b.2.val⟩, b.2.property⟩
  invFun b := ⟨b.val.1, ⟨b.val.2, b.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundaryReindex_dist (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : Sigma BoundaryComponent) :
    @dist BoundaryVertex (boundaryMetric S t).toDist (boundaryReindex x) (boundaryReindex y) =
      @dist (Sigma BoundaryComponent) (boundaryComponentsMetric S t).toDist x y := by
  let := componentMetric S t
  let := boundaryComponentMetric S t
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  change separatedDist fiberBoundaryBase
    ⟨i, boundaryFiberEmbedding i u⟩ ⟨j, boundaryFiberEmbedding j v⟩ =
      separatedDist boundaryRoot ⟨i, u⟩ ⟨j, v⟩
  by_cases hij : i = j
  · subst j
    simp only [separatedDist_same]
    rfl
  · rw [separatedDist_different fiberBoundaryBase hij, separatedDist_different boundaryRoot hij]
    rfl

theorem boundaryEdgeBound (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    (x y : BoundaryComponent j) (h : (boundaryGraph j).Adj x y) :
    @dist (BoundaryComponent j) (boundaryComponentMetric S t j).toDist x y ≤ 1 := by
  change @dist _ (componentMetric S t j).toDist
    (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y) ≤ 1
  rw [componentMetric_eq]
  change ((fiberedGraph S t j).dist (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y) : ℝ) ≤ 1
  exact_mod_cast (show (fiberedGraph S t j).dist (boundaryFiberEmbedding j x)
      (boundaryFiberEmbedding j y) ≤ 1 by
    simpa using (fiberedGraph S t j).dist_le (boundaryFiber_adj S t h).toWalk)

def boundaryFamilyMap (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (r : ℝ)
    (γ : ∀ j, C(WindingCircle,
      @Point (BoundaryComponent j) (boundaryComponentMetric S t j).toPseudoMetricSpace r)) :
    CocompactMap (Sigma (fun _ : ℕ => WindingCircle))
      (@Point BoundaryVertex (boundaryMetric S t).toPseudoMetricSpace r) := by
  let := boundaryComponentMetric S t
  let : ∀ j, PseudoMetricSpace (BoundaryComponent j) :=
    fun j => (boundaryComponentMetric S t j).toPseudoMetricSpace
  let := boundaryComponentsMetric S t
  let := boundaryMetric S t
  let : PseudoMetricSpace BoundaryVertex := (boundaryMetric S t).toPseudoMetricSpace
  exact (embeddingMap boundaryReindex.toEmbedding
    (fun x y => (boundaryReindex_dist S t x y).le) r).comp
      (ripsFamilyMap boundaryRoot r γ)

end CoarseAssembly

end

end OAI
