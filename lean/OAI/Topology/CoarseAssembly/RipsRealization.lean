import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.LocallyFinite
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-!
# Barycentric Rips realization and proper coarsening

Points are actual finitely supported probability weights with support of
bounded diameter. The topology is induced by the barycentric coordinates.
For a locally finite Rips complex this is its usual simplicial topology.
Increasing-scale inclusions are proved to be closed embeddings and therefore
proper, providing the continuous coarsening maps for analytic K-homology.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable (X : Type*) [PseudoMetricSpace X]

variable {X}

theorem coordinates_injective {r : ℝ} : Function.Injective (coordinates (X := X) (r := r)) := by
  intro p q h
  apply Point.ext
  exact Finsupp.ext (congrFun h)

theorem coordinates_continuous {r : ℝ} : Continuous (coordinates (X := X) (r := r)) :=
  continuous_induced_dom

theorem coordinate_continuous {r : ℝ} (x : X) :
    Continuous (fun p : Point X r => p.weight x) :=
  (continuous_apply x).comp coordinates_continuous

@[simp] theorem coarsen_weight {r s : ℝ} (h : r ≤ s) (p : Point X r) :
    (coarsen h p).weight = p.weight := rfl

theorem coarsen_embedding {r s : ℝ} (h : r ≤ s) : IsEmbedding (coarsen (X := X) h) where
  eq_induced := by
    change TopologicalSpace.induced coordinates _ =
      TopologicalSpace.induced (coarsen h) (TopologicalSpace.induced coordinates _)
    rw [induced_compose]
    rfl
  injective := by
    intro p q heq
    apply Point.ext
    exact congrArg (fun p : Point X s => p.weight) heq

theorem range_coarsen {r s : ℝ} (h : r ≤ s) :
    Set.range (coarsen (X := X) h) =
      {p : Point X s | ∀ x y, r < dist x y → p.weight x = 0 ∨ p.weight y = 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ x y hxy
    by_cases hx : q.weight x = 0
    · exact Or.inl hx
    by_cases hy : q.weight y = 0
    · exact Or.inr hy
    exact False.elim ((not_le_of_gt hxy)
      (q.diameter x (Finsupp.mem_support_iff.mpr hx) y (Finsupp.mem_support_iff.mpr hy)))
  · intro hp
    let q : Point X r :=
      { weight := p.weight
        nonneg := p.nonneg
        total := p.total
        diameter := by
          intro x hx y hy
          by_contra hxy
          rcases hp x y (lt_of_not_ge hxy) with hx' | hy'
          · exact Finsupp.mem_support_iff.mp hx hx'
          · exact Finsupp.mem_support_iff.mp hy hy' }
    exact ⟨q, by apply Point.ext; rfl⟩

theorem coarsen_closedEmbedding {r s : ℝ} (h : r ≤ s) :
    IsClosedEmbedding (coarsen (X := X) h) := by
  refine ⟨coarsen_embedding h, ?_⟩
  rw [range_coarsen h]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter (fun x => isClosed_iInter (fun y => isClosed_iInter (fun _ => ?_)))
  exact (isClosed_eq (coordinate_continuous x) continuous_const).union
    (isClosed_eq (coordinate_continuous y) continuous_const)

theorem inclusion_self (r : ℝ) (h : r ≤ r) :
    inclusion (X := X) h = CocompactMap.id (Point X r) := by
  apply CocompactMap.ext
  intro p
  apply Point.ext
  rfl

theorem inclusion_comp {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    inclusion (X := X) (hrs.trans hst) = (inclusion hst).comp (inclusion hrs) := by
  apply CocompactMap.ext
  intro p
  apply Point.ext
  rfl

end CoarseAssembly.Rips

end

end OAI
