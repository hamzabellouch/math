import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.Lattice
import OAI.Topology.CoarseAssembly.ShortLoops
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace OAI

/-!
# A combinatorial ray charge and the half-plane argument

We use a half-open cut along the positive horizontal ray: an edge entering
height zero from below has charge one exactly when its endpoint has positive
first coordinate. This is a combinatorial convention at ray vertices; edges
incident to the origin have charge zero. Its restriction to any of the six
open lattice half-planes is an exact difference of vertex potentials.
-/

namespace CoarseAssembly

@[simp] theorem latticeCharge_self (u : LatticeVertex) : latticeCharge u u = 0 := by
  simp only [latticeCharge]
  split_ifs <;> omega

theorem latticeCharge_reverse (u v : LatticeVertex) : latticeCharge v u = -latticeCharge u v := by
  simp only [latticeCharge]
  split_ifs <;> omega

theorem latticeCharge_abs_le (u v : LatticeVertex) : |latticeCharge u v| ≤ 1 := by
  simp only [latticeCharge]
  split_ifs <;> norm_num

inductive HexDirection
  | a | negA | b | negB | sum | negSum

def HexDirection.eval : HexDirection → LatticeVertex → ℤ
  | .a, u => u.1
  | .negA, u => -u.1
  | .b, u => u.2
  | .negB, u => -u.2
  | .sum, u => u.1 + u.2
  | .negSum, u => -(u.1 + u.2)

def HexDirection.potential : HexDirection → LatticeVertex → ℤ
  | .a, u | .sum, u => if 0 ≤ u.2 then 1 else 0
  | _, _ => 0

theorem HexDirection.adj_bound (d : HexDirection) {u v : LatticeVertex}
    (h : triangularGraph.Adj u v) : |d.eval u - d.eval v| ≤ 1 := by
  rcases h with ⟨ha, hb, hab, _⟩
  rw [abs_le] at ha hb hab ⊢
  cases d <;> simp only [HexDirection.eval] <;> omega

theorem HexDirection.radius_witness (u : LatticeVertex) :
    ∃ d : HexDirection, d.eval u = latticeRadius u := by
  simp only [latticeRadius]
  rcases le_total |u.1| |u.2| with h | h
  · rw [max_eq_right h]
    rcases le_total |u.2| |u.1 + u.2| with h' | h'
    · rw [max_eq_right h']
      by_cases hs : 0 ≤ u.1 + u.2
      · exact ⟨.sum, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negSum, (abs_of_neg (by omega)).symm⟩
    · rw [max_eq_left h']
      by_cases hs : 0 ≤ u.2
      · exact ⟨.b, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negB, (abs_of_neg (by omega)).symm⟩
  · rw [max_eq_left h]
    rcases le_total |u.1| |u.1 + u.2| with h' | h'
    · rw [max_eq_right h']
      by_cases hs : 0 ≤ u.1 + u.2
      · exact ⟨.sum, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negSum, (abs_of_neg (by omega)).symm⟩
    · rw [max_eq_left h']
      by_cases hs : 0 ≤ u.1
      · exact ⟨.a, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negA, (abs_of_neg (by omega)).symm⟩

/-- Exactness on all six open half-planes is the winding-zero argument,
including repeated edges and stationary projections. -/
theorem latticeCharge_halfPlane (d : HexDirection) {u v : LatticeVertex}
    (h : u = v ∨ triangularGraph.Adj u v) (hu : 0 < d.eval u) (hv : 0 < d.eval v) :
    latticeCharge u v = d.potential v - d.potential u := by
  rcases h with rfl | h
  · simp
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, e⟩
  simp only [triangularGraph, abs_le] at h
  cases d <;> simp only [HexDirection.eval, HexDirection.potential, latticeCharge] at * <;>
    split_ifs <;> omega

section ProjectedWalks

variable {V : Type*} {G : SimpleGraph V} (π : V → LatticeVertex)
variable (hπ : ∀ u v, G.Adj u v → π u = π v ∨ triangularGraph.Adj (π u) (π v))

include hπ

theorem projected_functional_bound (d : HexDirection) {u v : V} (p : G.Walk u v) :
    |d.eval (π u) - d.eval (π v)| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have he : |d.eval (π u) - d.eval (π v)| ≤ 1 := by
      rcases hπ u v h with he | he
      · simp [he]
      · exact d.adj_bound he
    calc
      _ ≤ |d.eval (π u) - d.eval (π v)| + |d.eval (π v) - d.eval (π w)| :=
        abs_sub_le _ _ _
      _ ≤ 1 + (p.length : ℤ) := add_le_add he ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℤ) := by simp; omega

theorem projected_charge_exact (d : HexDirection) {u v : V} (p : G.Walk u v)
    (hp : ∀ w ∈ p.support, 0 < d.eval (π w)) :
    walkCharge (fun u v => latticeCharge (π u) (π v)) p =
      d.potential (π v) - d.potential (π u) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hu := hp u (by simp)
    have htail : ∀ z ∈ p.support, 0 < d.eval (π z) := by
      intro z hz
      exact hp z (by simp [hz])
    rw [walkCharge_cons, latticeCharge_halfPlane d (hπ u v h) hu
      (htail v p.start_mem_support), ih htail]
    omega

/-- A charged closed path must meet the nonpositive side of every one of
the six linear functionals. -/
theorem charged_walk_meets_halfPlane (d : HexDirection) {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0) :
    ∃ w ∈ p.support, d.eval (π w) ≤ 0 := by
  by_contra h
  push Not at h
  have hz := projected_charge_exact π hπ d p h
  exact hc (by simpa using hz)

/-- The geometric estimate in the small-loop lemma. -/
theorem charged_walk_radius_bound {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0) :
    2 * latticeRadius (π u) ≤ (p.length : ℤ) := by
  obtain ⟨d, hd⟩ := HexDirection.radius_witness (π u)
  obtain ⟨w, hw, hf⟩ := charged_walk_meets_halfPlane π hπ d p hc
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hw
  have hq := projected_functional_bound π hπ d q
  have hr := projected_functional_bound π hπ d r
  rw [abs_le] at hq hr
  simp only [SimpleGraph.Walk.length_append, Nat.cast_add]
  omega

/-- The same estimate holds at every occurrence of a vertex, by rotating
the closed walk. No simplicity hypothesis is needed. -/
theorem charged_walk_all_radius_bound {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0)
    {w : V} (hw : w ∈ p.support) :
    2 * latticeRadius (π w) ≤ (p.length : ℤ) := by
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hw
  have hrot : walkCharge (fun u v => latticeCharge (π u) (π v)) (r.append q) ≠ 0 := by
    simpa only [walkCharge_append, add_comm] using hc
  have hb := charged_walk_radius_bound π hπ (r.append q) hrot
  simpa only [SimpleGraph.Walk.length_append, Nat.add_comm] using hb

end ProjectedWalks

end CoarseAssembly

end OAI
