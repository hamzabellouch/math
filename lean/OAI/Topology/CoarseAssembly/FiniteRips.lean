import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsPaths
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Compactness of finite Rips realizations

The finite Rips complex is a closed subset of the compact probability
simplex. In particular, its circle test has a compact domain.
-/

noncomputable section

namespace CoarseAssembly.Rips

open scoped BigOperators
open Topology

variable {X : Type*} [PseudoMetricSpace X] [Fintype X] (r : ℝ)

theorem range_coordinates :
    Set.range (coordinates (X := X) (r := r)) =
      {f : X → ℝ | (∀ x, 0 ≤ f x) ∧ (∑ x, f x) = 1 ∧
        ∀ x y, r < dist x y → f x = 0 ∨ f y = 0} := by
  classical
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.nonneg, p.sum_weight, ?_⟩
    intro x y hxy
    by_cases hx : p.weight x = 0
    · exact Or.inl hx
    by_cases hy : p.weight y = 0
    · exact Or.inr hy
    exact False.elim ((not_le_of_gt hxy)
      (p.diameter x (Finsupp.mem_support_iff.mpr hx) y (Finsupp.mem_support_iff.mpr hy)))
  · rintro ⟨hnn, ht, hd⟩
    let p : Point X r :=
      { weight := Finsupp.equivFunOnFinite.symm f
        nonneg := hnn
        total := by
          rw [Finsupp.sum_fintype _ _ (by simp)]
          exact ht
        diameter := by
          intro x hx y hy
          by_contra h
          rcases hd x y (lt_of_not_ge h) with hx' | hy'
          · exact Finsupp.mem_support_iff.mp hx hx'
          · exact Finsupp.mem_support_iff.mp hy hy' }
    exact ⟨p, rfl⟩

theorem coordinates_closed : IsClosed (Set.range (coordinates (X := X) (r := r))) := by
  rw [range_coordinates]
  have hnn : IsClosed {f : X → ℝ | ∀ x, 0 ≤ f x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
  have ht : IsClosed {f : X → ℝ | (∑ x, f x) = 1} :=
    isClosed_eq (continuous_finsetSum _ (fun x _ => continuous_apply x)) continuous_const
  have hd : IsClosed {f : X → ℝ | ∀ x y, r < dist x y → f x = 0 ∨ f y = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      (isClosed_eq (continuous_apply x) continuous_const).union
        (isClosed_eq (continuous_apply y) continuous_const)
  exact hnn.inter (ht.inter hd)

theorem coordinates_compact : IsCompact (Set.range (coordinates (X := X) (r := r))) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : X → ℝ)) (b := 1))
    (coordinates_closed r)
  rintro f ⟨p, rfl⟩
  refine ⟨p.nonneg, ?_⟩
  intro x
  calc
    p.weight x ≤ ∑ y : X, p.weight y := Finset.single_le_sum (fun y _ => p.nonneg y)
      (Finset.mem_univ x)
    _ = 1 := p.sum_weight

instance : SecondCountableTopology (Point X r) :=
  (show IsEmbedding (coordinates (X := X) (r := r)) from
    ⟨⟨rfl⟩, coordinates_injective⟩).secondCountableTopology

end CoarseAssembly.Rips

end

end OAI
