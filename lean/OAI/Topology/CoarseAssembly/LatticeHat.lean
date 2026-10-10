import OAI.Topology.CoarseAssembly.Lattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Piecewise linear hat functions of the triangular lattice

The nodal function at a lattice vertex is `max (0, 1 - ρ(p-v))`, where
`ρ(x,y) = max(|x|, |y|, |x+y|)`. These are the barycentric coordinate
functions for the filled triangular lattice. Their partition of unity
maps the filled hexagons into Rips space.
-/

noncomputable section

namespace CoarseAssembly

def realLatticeRadius (p : ℝ × ℝ) : ℝ := max (max |p.1| |p.2|) |p.1 + p.2|

theorem realLatticeRadius_le_iff {p : ℝ × ℝ} {a : ℝ} :
    realLatticeRadius p ≤ a ↔ |p.1| ≤ a ∧ |p.2| ≤ a ∧ |p.1 + p.2| ≤ a := by
  simp only [realLatticeRadius, max_le_iff, and_assoc]

theorem realLatticeRadius_lt_iff {p : ℝ × ℝ} {a : ℝ} :
    realLatticeRadius p < a ↔ |p.1| < a ∧ |p.2| < a ∧ |p.1 + p.2| < a := by
  simp only [realLatticeRadius, max_lt_iff, and_assoc]

theorem realLatticeRadius_continuous : Continuous realLatticeRadius := by
  unfold realLatticeRadius
  fun_prop

def hatKernel (x y : ℝ) : ℝ := max 0 (1 - realLatticeRadius (x, y))

def latticeHat (p : ℝ × ℝ) (v : LatticeVertex) : ℝ :=
  hatKernel (p.1 - v.1) (p.2 - v.2)

theorem latticeHat_nonneg (p : ℝ × ℝ) (v : LatticeVertex) : 0 ≤ latticeHat p v :=
  le_max_left _ _

theorem latticeHat_continuous (v : LatticeVertex) : Continuous (fun p => latticeHat p v) := by
  unfold latticeHat hatKernel realLatticeRadius
  fun_prop

theorem latticeHat_pos_iff (p : ℝ × ℝ) (v : LatticeVertex) :
    0 < latticeHat p v ↔
      |p.1 - v.1| < 1 ∧ |p.2 - v.2| < 1 ∧ |(p.1 - v.1) + (p.2 - v.2)| < 1 := by
  simp only [latticeHat, hatKernel, lt_max_iff, lt_self_iff_false, false_or,
    sub_pos, realLatticeRadius_lt_iff]

/-- The four cell functions sum to one; at most three of them are positive. -/
theorem hatKernel_partition {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hs₁ : s ≤ 1) (ht₁ : t ≤ 1) :
    hatKernel s t + hatKernel (s - 1) t + hatKernel s (t - 1) +
      hatKernel (s - 1) (t - 1) = 1 := by
  have r00 : realLatticeRadius (s, t) = s + t := by
    simp only [realLatticeRadius, abs_of_nonneg hs, abs_of_nonneg ht,
      abs_of_nonneg (add_nonneg hs ht)]
    rw [max_eq_right (max_le (by linarith) (by linarith))]
  have r11 : realLatticeRadius (s - 1, t - 1) = 2 - s - t := by
    rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
      abs_of_nonpos (by linarith : t - 1 ≤ 0),
      abs_of_nonpos (by linarith : s - 1 + (t - 1) ≤ 0)]
    rw [max_eq_right (max_le (by linarith) (by linarith))]
    ring
  by_cases hst : s + t ≤ 1
  · have r10 : realLatticeRadius (s - 1, t) = 1 - s := by
      rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
        abs_of_nonneg ht, abs_of_nonpos (by linarith : s - 1 + t ≤ 0)]
      rw [show max (-(s - 1)) t = -(s - 1) from max_eq_left (by linarith),
        max_eq_left (by linarith)]
      ring
    have r01 : realLatticeRadius (s, t - 1) = 1 - t := by
      rw [realLatticeRadius, abs_of_nonneg hs,
        abs_of_nonpos (by linarith : t - 1 ≤ 0),
        abs_of_nonpos (by linarith : s + (t - 1) ≤ 0)]
      rw [show max s (-(t - 1)) = -(t - 1) from max_eq_right (by linarith),
        max_eq_left (by linarith)]
      ring
    simp only [hatKernel, r00, r10, r01, r11]
    rw [max_eq_right (by linarith : 0 ≤ 1 - (s + t)),
      max_eq_right (by linarith : 0 ≤ 1 - (1 - s)),
      max_eq_right (by linarith : 0 ≤ 1 - (1 - t)),
      max_eq_left (by linarith : 1 - (2 - s - t) ≤ 0)]
    ring
  · have r10 : realLatticeRadius (s - 1, t) = t := by
      rw [realLatticeRadius, abs_of_nonpos (by linarith : s - 1 ≤ 0),
        abs_of_nonneg ht, abs_of_nonneg (by linarith : 0 ≤ s - 1 + t)]
      rw [show max (-(s - 1)) t = t from max_eq_right (by linarith),
        max_eq_left (by linarith)]
    have r01 : realLatticeRadius (s, t - 1) = s := by
      rw [realLatticeRadius, abs_of_nonneg hs,
        abs_of_nonpos (by linarith : t - 1 ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ s + (t - 1))]
      rw [show max s (-(t - 1)) = s from max_eq_left (by linarith),
        max_eq_left (by linarith)]
    simp only [hatKernel, r00, r10, r01, r11]
    rw [max_eq_left (by linarith : 1 - (s + t) ≤ 0),
      max_eq_right (by linarith : 0 ≤ 1 - t), max_eq_right (by linarith : 0 ≤ 1 - s),
      max_eq_right (by linarith : 0 ≤ 1 - (2 - s - t))]
    ring

def latticeCell (p : ℝ × ℝ) : Finset LatticeVertex :=
  ({⌊p.1⌋, ⌊p.1⌋ + 1} : Finset ℤ) ×ˢ ({⌊p.2⌋, ⌊p.2⌋ + 1} : Finset ℤ)

theorem latticeHat_support_cell (p : ℝ × ℝ) (v : LatticeVertex)
    (hv : latticeHat p v ≠ 0) : v ∈ latticeCell p := by
  have hp := (latticeHat_pos_iff p v).mp (lt_of_le_of_ne (latticeHat_nonneg p v) hv.symm)
  have bound (x : ℝ) (n : ℤ) (h : |x - n| < 1) : n = ⌊x⌋ ∨ n = ⌊x⌋ + 1 := by
    have hf := Int.floor_le x
    have hc := Int.lt_floor_add_one x
    rw [abs_lt] at h
    have hlow : ⌊x⌋ < n + 1 := by exact_mod_cast (show (⌊x⌋ : ℝ) < (n : ℝ) + 1 by linarith)
    have hupp : n < ⌊x⌋ + 2 := by exact_mod_cast (show (n : ℝ) < (⌊x⌋ : ℝ) + 2 by linarith)
    omega
  simpa only [latticeCell, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    using And.intro (bound p.1 v.1 hp.1) (bound p.2 v.2 hp.2.1)

def latticeHatWeights (p : ℝ × ℝ) : LatticeVertex →₀ ℝ :=
  Finsupp.onFinset (latticeCell p) (latticeHat p) (latticeHat_support_cell p)

@[simp] theorem latticeHatWeights_apply (p : ℝ × ℝ) (v : LatticeVertex) :
    latticeHatWeights p v = latticeHat p v := rfl

theorem latticeHatWeights_total (p : ℝ × ℝ) :
    (latticeHatWeights p).sum (fun _ t => t) = 1 := by
  classical
  rw [latticeHatWeights, Finsupp.onFinset_sum (latticeHat_support_cell p) (by simp)]
  have hx : (⌊p.1⌋ : ℤ) ≠ ⌊p.1⌋ + 1 := by omega
  have hy : (⌊p.2⌋ : ℤ) ≠ ⌊p.2⌋ + 1 := by omega
  have hs : 0 ≤ p.1 - (⌊p.1⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.1)
  have ht : 0 ≤ p.2 - (⌊p.2⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.2)
  have hs₁ : p.1 - (⌊p.1⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.1]
  have ht₁ : p.2 - (⌊p.2⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.2]
  have h := hatKernel_partition hs ht hs₁ ht₁
  simp only [latticeCell, Finset.sum_product, Finset.sum_insert (Finset.notMem_singleton.mpr hx),
    Finset.sum_insert (Finset.notMem_singleton.mpr hy), Finset.sum_singleton, latticeHat,
    Int.cast_add, Int.cast_one, sub_add_eq_sub_sub]
  linarith

theorem latticeHat_adjacent {p : ℝ × ℝ} {v w : LatticeVertex}
    (hv : 0 < latticeHat p v) (hw : 0 < latticeHat p w) :
    v = w ∨ triangularGraph.Adj v w := by
  by_cases h : v = w
  · exact Or.inl h
  right
  have hv' := (latticeHat_pos_iff p v).mp hv
  have hw' := (latticeHat_pos_iff p w).mp hw
  have bound (a b x : ℝ) (ha : |x - a| < 1) (hb : |x - b| < 1) : |a - b| < 2 := by
    rw [abs_lt] at ha hb ⊢
    constructor <;> linarith
  have hab : |v.1 - w.1| < 2 := by exact_mod_cast bound (v.1 : ℝ) w.1 p.1 hv'.1 hw'.1
  have hbc : |v.2 - w.2| < 2 := by exact_mod_cast bound (v.2 : ℝ) w.2 p.2 hv'.2.1 hw'.2.1
  have hs : |(v.1 + v.2) - (w.1 + w.2)| < 2 := by
    have hvsum : |(p.1 + p.2) - ((v.1 : ℝ) + v.2)| < 1 := by
      convert hv'.2.2 using 1
      congr 1
      ring
    have hwsum : |(p.1 + p.2) - ((w.1 : ℝ) + w.2)| < 1 := by
      convert hw'.2.2 using 1
      congr 1
      ring
    exact_mod_cast bound ((v.1 : ℝ) + v.2) ((w.1 : ℝ) + w.2) (p.1 + p.2) hvsum hwsum
  exact ⟨by omega, by omega, by omega, h⟩

theorem latticeHat_in_disc {j : ℕ} {p : ℝ × ℝ}
    (hp : realLatticeRadius p ≤ j) {v : LatticeVertex} (hv : 0 < latticeHat p v) :
    latticeRadius v ≤ j := by
  have hp' := realLatticeRadius_le_iff.mp hp
  have hv' := (latticeHat_pos_iff p v).mp hv
  have bound (x n : ℝ) (hx : |x| ≤ j) (hn : |x - n| < 1) : |n| < (j : ℝ) + 1 := by
    rw [abs_le] at hx
    rw [abs_lt] at hn ⊢
    constructor <;> linarith
  have ha : |v.1| < (j : ℤ) + 1 := by exact_mod_cast bound p.1 v.1 hp'.1 hv'.1
  have hb : |v.2| < (j : ℤ) + 1 := by exact_mod_cast bound p.2 v.2 hp'.2.1 hv'.2.1
  have hc : |v.1 + v.2| < (j : ℤ) + 1 := by
    have hsum : |(p.1 + p.2) - ((v.1 : ℝ) + v.2)| < 1 := by
      convert hv'.2.2 using 1
      congr 1
      ring
    exact_mod_cast bound (p.1 + p.2) ((v.1 : ℝ) + v.2) hp'.2.2 hsum
  simp only [latticeRadius, max_le_iff]
  omega

end CoarseAssembly

end

end OAI
