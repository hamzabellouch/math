import OAI.RingTheory.DirectFiniteness.FiniteAffine

namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
namespace KaplanskyCounterexample.FiniteGeometry

variable {α : Type u_1} {ι : Type u_2} [Fintype α]

/-- Independent selection of points at a prescribed probability. -/
def selectionMeasure (p : Set.Icc (0 : ℝ) 1) : Measure (α → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false p

instance (p : Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (selectionMeasure (α := α) p) := by
  unfold selectionMeasure
  infer_instance

def allSelected (s : Finset α) : Set (α → Bool) := {ω | ∀ x ∈ s, ω x = true}

lemma probability_allSelected (p : Set.Icc (0 : ℝ) 1) (s : Finset α) :
    (selectionMeasure p).real (allSelected s) = p.val ^ s.card := by
  change (Measure.pi (fun _ : α => bernoulliMeasure true false p)).real
    ((s : Set α).pi fun _ => {true}) = _
  rw [Measure.real, Measure.pi_pi_finset, ENNReal.toReal_prod]
  have hval : (bernoulliMeasure true false p).real {true} = p.val := by
    apply bernoulliMeasure_real_apply_of_mem_of_notMem
    · simp
    · simp
    · simp
  simp only [← measureReal_def, hval, Finset.prod_const, Finset.card_eq_sum_ones]

lemma integral_selection_indicator (p : Set.Icc (0 : ℝ) 1) (s : Finset α) :
    (∫ ω, (if ω ∈ allSelected s then (1 : ℝ) else 0) ∂selectionMeasure p) =
      p.val ^ s.card := by
  have hm : MeasurableSet (allSelected s) := (Set.toFinite _).countable.measurableSet
  change (∫ ω, (allSelected s).indicator (fun _ => (1 : ℝ)) ω ∂selectionMeasure p) = _
  calc
    _ = (selectionMeasure p).real (allSelected s) := by
      simpa only [Pi.one_def] using integral_indicator_one (μ := selectionMeasure p) hm
    _ = _ := probability_allSelected p s

/-- Finite probabilistic alteration: delete all vertices in every fully chosen
forbidden set. Duplicate forbidden sets are permitted, and only strengthen the
upper bound on expected deletions. -/
theorem exists_avoiding_card [Fintype ι] (C : ι → Finset α)
    (hne : ∀ i, (C i).Nonempty) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset α, (∀ i, ¬ C i ⊆ O) ∧
      (Fintype.card α : ℝ) * p.val - ∑ i, (C i).card * p.val ^ (C i).card ≤ O.card := by
  let X (ω : α → Bool) : Finset α := Finset.univ.filter fun x => ω x = true
  let marks (ω : α → Bool) : Finset α :=
    Finset.univ.biUnion fun i => if C i ⊆ X ω then C i else ∅
  let cost (ω : α → Bool) : ℕ := ∑ i, if C i ⊆ X ω then (C i).card else 0
  let gain (ω : α → Bool) : ℝ := (X ω).card - cost ω
  have hmem (s : Finset α) (ω : α → Bool) : s ⊆ X ω ↔ ω ∈ allSelected s := by
    simp [X, Finset.subset_iff, allSelected]
  have hX (ω : α → Bool) : ((X ω).card : ℝ) =
      ∑ x : α, if ω ∈ allSelected {x} then (1 : ℝ) else 0 := by
    simp only [X, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    simp [allSelected]
  have hcost (ω : α → Bool) : (cost ω : ℝ) =
      ∑ i, (C i).card * if ω ∈ allSelected (C i) then (1 : ℝ) else 0 := by
    simp [cost, Nat.cast_sum, hmem]
  have hmean : (∫ ω, gain ω ∂selectionMeasure p) =
      (Fintype.card α : ℝ) * p.val - ∑ i, (C i).card * p.val ^ (C i).card := by
    simp_rw [gain, hX, hcost]
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp_rw [integral_const_mul, integral_selection_indicator]
    simp
  obtain ⟨ω, hω⟩ := exists_integral_le (μ := selectionMeasure p)
    (f := gain) Integrable.of_finite
  refine ⟨X ω \ marks ω, ?_, ?_⟩
  · intro i hi
    obtain ⟨x, hx⟩ := hne i
    have hxi := hi hx
    have hCX : C i ⊆ X ω := fun y hy => (Finset.mem_sdiff.mp (hi hy)).1
    have hmarked : x ∈ marks ω := by
      simp only [marks, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, by simpa [hCX] using hx⟩
    exact (Finset.mem_sdiff.mp hxi).2 hmarked
  · rw [hmean] at hω
    refine hω.trans ?_
    have hm : (marks ω).card ≤ cost ω := by
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp_all
    have hc := Finset.card_sdiff_add_card_inter (X ω) (marks ω)
    have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := X ω) (s₂ := marks ω))
    have hn : (X ω).card ≤ (X ω \ marks ω).card + cost ω := by omega
    have hr : ((X ω).card : ℝ) ≤ (X ω \ marks ω).card + cost ω := by exact_mod_cast hn
    dsimp [gain]
    linarith

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
