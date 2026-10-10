import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsEmbedding
import OAI.Topology.CoarseAssembly.SeparatedUnion
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Late components are clopen at a fixed Rips scale

This proves the topological component separation required for the changing
finite-component winding test in the actual separated coarse union.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)]

theorem separatedComponent_isometry (o : ∀ j, V j) (j : ℕ) :
    letI := separatedMetric o
    Isometry (separatedComponent (V := V) j) := by
  let := separatedMetric o
  apply Isometry.of_dist_eq
  intro x y
  exact separatedDist_same o j x y

theorem separatedComponent_separation (o : ∀ j, V j) (j : ℕ) (r : ℝ) (hj : r < j) :
    letI := separatedMetric o
    ∀ x y, y ∉ Set.range (separatedComponent (V := V) j) →
      r < dist (separatedComponent j x) y := by
  let := separatedMetric o
  rintro x ⟨k, y⟩ hy
  have hjk : j ≠ k := by
    rintro rfl
    exact hy ⟨y, rfl⟩
  change r < separatedDist o ⟨j, x⟩ ⟨k, y⟩
  rw [separatedDist_different o hjk]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith [dist_nonneg (x := x) (y := o j), dist_nonneg (x := o k) (y := y)]

theorem separated_closedBall_finite [∀ j, Fintype (V j)]
    (o : ∀ j, V j) (x : Sigma V) (r : ℝ) :
    letI := separatedMetric o
    Set.Finite {y : Sigma V | dist x y ≤ r} := by
  classical
  let := separatedMetric o
  let m := max (x.1 + 1) (⌈r⌉₊ + 1)
  let s : Finset (Sigma V) := (Finset.range m).sigma (fun _ => Finset.univ)
  apply s.finite_toSet.subset
  intro y hy
  have hm : y.1 < m := by
    by_cases hxy : x.1 = y.1
    · dsimp [m]
      omega
    · have hb := (separatedDist_indices o x y hxy hy).2
      have hc : y.1 ≤ ⌈r⌉₊ := by exact_mod_cast hb.trans (Nat.le_ceil r)
      dsimp [m]
      omega
  exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hm, Finset.mem_univ _⟩

/-- The chosen late finite Rips component really is open and closed in
the global Rips realization; its inclusion is continuous and proper. -/
theorem lateRipsComponent_openEmbedding [∀ j, Fintype (V j)]
    (o : ∀ j, V j) (j : ℕ) (r : ℝ) (hj : r < j) :
    letI := separatedMetric o
    IsOpenEmbedding (mapPoint (r := r) (separatedComponent (V := V) j)
      (fun x y => ((separatedComponent_isometry o j).dist_eq x y).le)) := by
  let := separatedMetric o
  exact
    { toIsEmbedding := (mapPoint_closedEmbedding _ _).isEmbedding
      isOpen_range := mapPoint_range_open _ (separatedComponent_isometry o j)
        (separatedComponent_separation o j r hj) }

end CoarseAssembly

end

end OAI
