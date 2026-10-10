import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Group.MinMax

namespace OAI

/-!
# The triangular-lattice discs

The vertex set, adjacency, radius and depth used in §3 of the coarse Novikov
manuscript. The three integer linear forms are precisely those in its hexagonal
radius `max {|a|, |b|, |a+b|}`. These definitions do not assert the unproved
identification of the filled geometric realization with a topological disc.
-/

namespace CoarseAssembly

theorem latticeRadius_nonneg (u : LatticeVertex) : 0 ≤ latticeRadius u := by
  exact (abs_nonneg _).trans (le_max_right _ _)

def latticeNeighbors (u : LatticeVertex) : Finset LatticeVertex :=
  {(u.1 + 1, u.2), (u.1 - 1, u.2), (u.1, u.2 + 1),
    (u.1, u.2 - 1), (u.1 + 1, u.2 - 1), (u.1 - 1, u.2 + 1)}

theorem mem_latticeNeighbors_iff (u v : LatticeVertex) :
    v ∈ latticeNeighbors u ↔ triangularGraph.Adj u v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  simp only [latticeNeighbors, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    triangularGraph, abs_le, ne_eq, Prod.mk.injEq]
  omega

theorem card_latticeNeighbors_le (u : LatticeVertex) : (latticeNeighbors u).card ≤ 6 := by
  unfold latticeNeighbors
  exact le_trans (Finset.card_insert_le _ _) (by
    apply Nat.succ_le_succ
    exact le_trans (Finset.card_insert_le _ _) (by
      apply Nat.succ_le_succ
      exact le_trans (Finset.card_insert_le _ _) (by
        apply Nat.succ_le_succ
        exact le_trans (Finset.card_insert_le _ _) (by
          apply Nat.succ_le_succ
          exact le_trans (Finset.card_insert_le _ _) (by simp)))))

/-- Radius changes by at most one across a lattice edge. -/
theorem latticeRadius_adj {u v : LatticeVertex} (h : triangularGraph.Adj u v) :
    |latticeRadius u - latticeRadius v| ≤ 1 := by
  unfold latticeRadius
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · apply (abs_max_sub_max_le_max _ _ _ _).trans
    exact max_le ((abs_abs_sub_abs_le_abs_sub _ _).trans h.1)
      ((abs_abs_sub_abs_le_abs_sub _ _).trans h.2.1)
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans h.2.2.1

theorem finite_disc (j : ℕ) : {u : LatticeVertex | latticeRadius u ≤ (j : ℤ)}.Finite := by
  apply ((Set.finite_Icc (-(j : ℤ)) j).prod (Set.finite_Icc (-(j : ℤ)) j)).subset
  intro u hu
  simp only [Set.mem_ofPred_eq, latticeRadius, max_le_iff, abs_le] at hu
  exact ⟨hu.1.1, hu.1.2⟩

instance (j : ℕ) : Inhabited (Disc j) :=
  ⟨⟨(0, 0), by simp [latticeRadius]⟩⟩

theorem discDepth_int (j : ℕ) (u : Disc j) :
    (discDepth j u : ℤ) = (j : ℤ) - latticeRadius u.val := by
  exact Int.toNat_of_nonneg (sub_nonneg.mpr u.property)

theorem discDepth_adj {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v) :
    |(discDepth j u : ℤ) - (discDepth j v : ℤ)| ≤ 1 := by
  rw [discDepth_int, discDepth_int]
  have hr := latticeRadius_adj h
  rw [abs_le] at hr ⊢
  omega

theorem discDepth_eq_zero_iff (j : ℕ) (u : Disc j) :
    discDepth j u = 0 ↔ latticeRadius u.val = j := by
  have hd := discDepth_int j u
  omega

end CoarseAssembly

end OAI
