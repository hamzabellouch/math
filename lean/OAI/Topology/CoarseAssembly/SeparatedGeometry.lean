import OAI.Topology.CoarseAssembly.SeparatedUnion
import OAI.Topology.CoarseAssembly.TransferCriterion
import Mathlib.Data.Finset.Sigma

namespace OAI

/-! # Bounded geometry of the separated union

Uniform component ball bounds pass to the union. All cross-component pairs
in a fixed distance range lie in a finite prefix, which also supplies the
finite exceptional set in the transfer argument.
-/

noncomputable section

namespace CoarseAssembly

variable {V : ℕ → Type*} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]

def componentPrefix (N : ℕ) : Finset (Sigma V) :=
  (Finset.range (N + 1)).sigma (fun _ => Finset.univ)

omit [∀ i, MetricSpace (V i)] in
@[simp] theorem mem_componentPrefix (N : ℕ) (x : Sigma V) :
    x ∈ componentPrefix N ↔ x.1 ≤ N := by
  classical
  simp only [componentPrefix, Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true,
    Nat.lt_succ_iff]

theorem finite_cross_pairs (o : ∀ i, V i) (R : ℝ) :
    {p : Sigma V × Sigma V | p.1.1 ≠ p.2.1 ∧ separatedDist o p.1 p.2 ≤ R}.Finite := by
  apply ((componentPrefix (V := V) ⌈R⌉₊).finite_toSet.prod
    (componentPrefix (V := V) ⌈R⌉₊).finite_toSet).subset
  intro p hp
  obtain ⟨hx, hy⟩ := separatedDist_indices o p.1 p.2 hp.1 hp.2
  have hR : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  exact ⟨(mem_componentPrefix _ _).mpr (by exact_mod_cast hx.trans hR),
    (mem_componentPrefix _ _).mpr (by exact_mod_cast hy.trans hR)⟩

/-- The bounded-geometry hypothesis needed by the Roe transfer is preserved
by this separated union. -/
theorem separated_uniform_finite_balls (o : ∀ i, V i)
    (hcomp : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ, ∀ i (x : V i), ∃ b : Finset (V i),
      (∀ y, y ∈ b ↔ dist x y ≤ R) ∧ b.card ≤ N) :
    @UniformFiniteBalls (Sigma V) (separatedMetric o).toPseudoMetricSpace := by
  classical
  let := separatedMetric o
  intro R hR
  obtain ⟨N, hN⟩ := hcomp R hR
  refine ⟨N + (componentPrefix (V := V) ⌈R⌉₊).card, ?_⟩
  rintro ⟨i, x⟩
  obtain ⟨b, hb, hcard⟩ := hN i x
  let emb : V i ↪ Sigma V := ⟨Sigma.mk i, fun _ _ h => by simpa using h⟩
  let c := b.map emb ∪ componentPrefix (V := V) ⌈R⌉₊
  refine ⟨c.filter (fun y => dist (⟨i, x⟩ : Sigma V) y ≤ R), ?_, ?_⟩
  · intro y
    simp only [Finset.mem_filter]
    refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
    rcases y with ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      apply Finset.mem_union_left
      apply Finset.mem_map.mpr
      refine ⟨y, (hb y).mpr ?_, rfl⟩
      change separatedDist o ⟨i, x⟩ ⟨i, y⟩ ≤ R at hy
      simpa only [separatedDist_same] using hy
    · apply Finset.mem_union_right
      apply (mem_componentPrefix _ _).mpr
      have hi := (separatedDist_indices o ⟨i, x⟩ ⟨j, y⟩ hij hy).2
      exact_mod_cast hi.trans (Nat.le_ceil R)
  · calc
      _ ≤ c.card := Finset.card_filter_le _ _
      _ ≤ (b.map emb).card + (componentPrefix (V := V) ⌈R⌉₊).card := Finset.card_union_le _ _
      _ ≤ N + (componentPrefix (V := V) ⌈R⌉₊).card := by
        rw [Finset.card_map]
        exact Nat.add_le_add_right hcard _

omit [∀ i, Fintype (V i)] in
/-- Unit separation in each component gives unit separation in the union. -/
theorem separated_uniform_discrete (o : ∀ i, V i)
    (hcomp : ∀ i (x y : V i), x ≠ y → 1 ≤ dist x y)
    (x y : Sigma V) (hxy : x ≠ y) : 1 ≤ separatedDist o x y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [separatedDist_same]
    exact hcomp i x y (fun h => hxy (congrArg (Sigma.mk i) h))
  · rw [separatedDist_different o hij]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [dist_nonneg (x := x) (y := o i), dist_nonneg (x := o j) (y := y)]

end CoarseAssembly

end

end OAI
