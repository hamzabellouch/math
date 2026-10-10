import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! # A separated metric union

Components embed isometrically. Paths between different components go
through chosen roots, with bridge length `i + j + 2`; thus bounded-distance
cross-component pairs lie in finitely many finite components.
-/

noncomputable section

namespace CoarseAssembly

variable {V : ℕ → Type*} [∀ i, MetricSpace (V i)]

@[simp] theorem separatedDist_same (o : ∀ i, V i) (i : ℕ) (x y : V i) :
    separatedDist o ⟨i, x⟩ ⟨i, y⟩ = dist x y := dite_eq_left rfl

theorem separatedDist_different (o : ∀ i, V i) {i j : ℕ} (h : i ≠ j)
    (x : V i) (y : V j) :
    separatedDist o ⟨i, x⟩ ⟨j, y⟩ =
      dist x (o i) + ((i : ℝ) + (j : ℝ) + 2) + dist (o j) y := dite_eq_right h

theorem separatedDist_comm (o : ∀ i, V i) (x y : Sigma V) :
    separatedDist o x y = separatedDist o y x := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases h : i = j
  · subst j; simp only [separatedDist_same, dist_comm]
  · rw [separatedDist_different o h, separatedDist_different o (Ne.symm h)]
    simp only [dist_comm y (o j), dist_comm (o i) x]
    ring

theorem separatedDist_triangle (o : ∀ i, V i) (x y z : Sigma V) :
    separatedDist o x z ≤ separatedDist o x y + separatedDist o y z := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k; simp only [separatedDist_same]; exact dist_triangle _ _ _
    · simp only [separatedDist_same, separatedDist_different o hik]
      linarith [dist_triangle x y (o i)]
  · by_cases hjk : j = k
    · subst k
      simp only [separatedDist_same, separatedDist_different o hij]
      linarith [dist_triangle (o j) y z]
    · by_cases hik : i = k
      · subst k
        simp only [separatedDist_same, separatedDist_different o hij,
          separatedDist_different o (Ne.symm hij)]
        have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith [dist_triangle x (o i) z, dist_nonneg (x := y) (y := o j),
          dist_nonneg (x := o j) (y := y)]
      · simp only [separatedDist_different o hik, separatedDist_different o hij,
          separatedDist_different o hjk]
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith [dist_nonneg (x := y) (y := o j), dist_nonneg (x := o j) (y := y)]

theorem separatedDist_indices (o : ∀ i, V i) (x y : Sigma V) (hxy : x.1 ≠ y.1)
    {R : ℝ} (hR : separatedDist o x y ≤ R) : (x.1 : ℝ) ≤ R ∧ (y.1 : ℝ) ≤ R := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rw [separatedDist_different o hxy] at hR
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> linarith [dist_nonneg (x := x) (y := o i), dist_nonneg (x := o j) (y := y)]

end CoarseAssembly

end

end OAI
