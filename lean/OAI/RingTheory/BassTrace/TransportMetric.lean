import OAI.RingTheory.BassTrace.ActivatedUnions

namespace OAI

/-! The dual transportation metric on finitely supported probability vectors. -/

namespace BassTrace.Sparse

open Finset

structure FinProbability (Y : Type*) where
  coeff : Y →₀ ℝ
  nonneg : ∀ y, 0 ≤ coeff y
  total : coeff.sum (fun _ r => r) = 1

namespace FinProbability

variable {Y : Type*}

@[ext] theorem ext_coeff {p q : FinProbability Y} (h : p.coeff = q.coeff) : p = q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def expectation (p : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.coeff.sum fun y r => r * f y

lemma expectation_const (p : FinProbability Y) (c : ℝ) :
    p.expectation (fun _ => c) = c := by
  classical
  unfold expectation Finsupp.sum at *
  rw [← Finset.sum_mul, show (∑ y ∈ p.coeff.support, p.coeff y) = 1 from p.total, one_mul]

lemma expectation_add (p : FinProbability Y) (f g : Y → ℝ) :
    p.expectation (fun y => f y + g y) = p.expectation f + p.expectation g := by
  classical
  simp [expectation, Finsupp.sum, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : FinProbability Y) (f g : Y → ℝ) :
    p.expectation (fun y => f y - g y) = p.expectation f - p.expectation g := by
  classical
  simp [expectation, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]

lemma expectation_neg (p : FinProbability Y) (f : Y → ℝ) :
    p.expectation (-f) = - p.expectation f := by
  classical
  simp [expectation, Finsupp.sum]

lemma expectation_mono (p : FinProbability Y) {f g : Y → ℝ} (h : ∀ y, f y ≤ g y) :
    p.expectation f ≤ p.expectation g := by
  classical
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (p.nonneg y)

lemma expectation_nonneg (p : FinProbability Y) {f : Y → ℝ} (h : ∀ y, 0 ≤ f y) :
    0 ≤ p.expectation f := by
  classical
  exact Finset.sum_nonneg fun y _ => mul_nonneg (p.nonneg y) (h y)

lemma abs_expectation_le (p : FinProbability Y) (f : Y → ℝ) :
    |p.expectation f| ≤ p.expectation (fun y => |f y|) := by
  classical
  unfold expectation Finsupp.sum
  calc
    |∑ y ∈ p.coeff.support, p.coeff y * f y|
      ≤ ∑ y ∈ p.coeff.support, |p.coeff y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ p.coeff.support, p.coeff y * |f y| := by
      congr 1
      funext y
      rw [abs_mul, abs_of_nonneg (p.nonneg y)]

noncomputable def gap (p q : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.expectation f - q.expectation f

lemma gap_const (p q : FinProbability Y) (c : ℝ) : p.gap q (fun _ => c) = 0 := by
  simp [gap, expectation_const]

lemma gap_sub_const (p q : FinProbability Y) (f : Y → ℝ) (c : ℝ) :
    p.gap q (fun y => f y - c) = p.gap q f := by
  simp only [gap, expectation_sub, expectation_const]
  ring

lemma gap_neg (p q : FinProbability Y) (f : Y → ℝ) :
    p.gap q (-f) = -p.gap q f := by
  simp only [gap, expectation_neg]
  ring

lemma gap_add (p q : FinProbability Y) (f g : Y → ℝ) :
    p.gap q (f + g) = p.gap q f + p.gap q g := by
  rw [gap, show f + g = fun y => f y + g y from rfl,
    expectation_add, expectation_add]
  simp only [gap]
  ring

lemma gap_telescope (p q r : FinProbability Y) (f : Y → ℝ) :
    p.gap r f = p.gap q f + q.gap r f := by
  simp only [gap]
  ring

lemma coeff_support_nonempty (p : FinProbability Y) : p.coeff.support.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : p.coeff = 0 := Finsupp.support_eq_empty.mp he
  have ht := p.total
  simp [hz] at ht

lemma gap_bound [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) (o : Y) :
    |p.gap q f| ≤ p.expectation (fun y => dist y o) +
      q.expectation (fun y => dist y o) := by
  rw [← gap_sub_const p q f (f o)]
  unfold gap
  calc
    |p.expectation (fun y => f y - f o) - q.expectation (fun y => f y - f o)|
      ≤ |p.expectation (fun y => f y - f o)| +
        |q.expectation (fun y => f y - f o)| := abs_sub _ _
    _ ≤ p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o) := by
      apply add_le_add
      · apply (p.abs_expectation_le _).trans
        apply p.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o
      · apply (q.abs_expectation_le _).trans
        apply q.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o

noncomputable def transport [PseudoMetricSpace Y] (p q : FinProbability Y) : ℝ :=
  sSup {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}

lemma potential_values_nonempty [PseudoMetricSpace Y] (p q : FinProbability Y) :
    {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}.Nonempty := by
  refine ⟨0, fun _ => 0, (LipschitzWith.const 0).weaken (by norm_num), ?_⟩
  exact gap_const p q 0

lemma potential_values_bddAbove [PseudoMetricSpace Y] (p q : FinProbability Y) :
    BddAbove {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r} := by
  classical
  obtain ⟨o, _⟩ := p.coeff_support_nonempty
  refine ⟨p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o), ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (le_abs_self _).trans (gap_bound p q f hf o)

lemma gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : p.gap q f ≤ p.transport q :=
  le_csSup (potential_values_bddAbove p q) ⟨f, hf, rfl⟩

lemma abs_gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : |p.gap q f| ≤ p.transport q := by
  apply abs_le.mpr
  constructor
  · have h := gap_le_transport p q (-f) hf.neg
    rw [gap_neg] at h
    linarith
  · exact gap_le_transport p q f hf

lemma transport_nonneg [PseudoMetricSpace Y] (p q : FinProbability Y) :
    0 ≤ p.transport q := by
  simpa [gap_const] using gap_le_transport p q (fun _ => 0) ((LipschitzWith.const 0).weaken (by norm_num))

lemma transport_le [PseudoMetricSpace Y] (p q : FinProbability Y) (b : ℝ)
    (h : ∀ f : Y → ℝ, LipschitzWith 1 f → p.gap q f ≤ b) : p.transport q ≤ b := by
  apply csSup_le (potential_values_nonempty p q)
  rintro r ⟨f, hf, rfl⟩
  exact h f hf

lemma transport_self [PseudoMetricSpace Y] (p : FinProbability Y) : p.transport p = 0 := by
  apply le_antisymm _ (transport_nonneg p p)
  apply transport_le
  intro f _
  simp [gap]

lemma transport_triangle [PseudoMetricSpace Y] (p q r : FinProbability Y) :
    p.transport r ≤ p.transport q + q.transport r := by
  apply transport_le
  intro f hf
  rw [gap_telescope p q r f]
  exact add_le_add (gap_le_transport p q f hf) (gap_le_transport q r f hf)

lemma transport_comm [PseudoMetricSpace Y] (p q : FinProbability Y) :
    p.transport q = q.transport p := by
  suffices ∀ p q : FinProbability Y, p.transport q ≤ q.transport p from
    le_antisymm (this p q) (this q p)
  intro p q
  apply transport_le
  intro f hf
  have h := gap_le_transport q p (-f) hf.neg
  simp only [gap, expectation_neg] at *
  linarith

lemma expectation_vertex_indicator [DecidableEq Y] (p : FinProbability Y) (v : Y) :
    p.expectation (fun y => if y = v then (1 : ℝ) else 0) = p.coeff v := by
  classical
  simp only [expectation, Finsupp.sum, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

lemma coordinate_control [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) (v : Y) :
    |p.coeff v - q.coeff v| ≤ p.transport q := by
  classical
  let f : Y → ℝ := fun y => if y = v then 1 else 0
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [NNReal.coe_one, one_mul]
    by_cases hy : y = v <;> by_cases hz : z = v
    · simp [f, hy, hz]
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hz (h ▸ hy))
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hy (h.symm ▸ hz))
    · simp [f, hy, hz]
  simpa only [gap, f, expectation_vertex_indicator] using abs_gap_le_transport p q f hf

lemma transport_eq_zero_iff [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : p.transport q = 0 ↔ p = q := by
  constructor
  · intro h
    apply ext_coeff
    ext v
    have hv := coordinate_control p q hdiscrete v
    rw [h] at hv
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))
  · rintro rfl
    exact transport_self _

lemma expectation_eq_zero_of_support (p : FinProbability Y) (f : Y → ℝ)
    (hf : ∀ y ∈ p.coeff.support, f y = 0) : p.expectation f = 0 := by
  classical
  unfold expectation Finsupp.sum
  exact Finset.sum_eq_zero fun y hy => by
    change p.coeff y * f y = 0
    rw [hf y hy, mul_zero]

lemma exists_support_le_expectation (p : FinProbability Y) (f : Y → ℝ) :
    ∃ y ∈ p.coeff.support, f y ≤ p.expectation f := by
  classical
  by_contra! h
  have hlt : p.expectation (fun _ => p.expectation f) < p.expectation f := by
    unfold expectation Finsupp.sum
    apply Finset.sum_lt_sum
    · intro y hy
      exact (mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))).le
    · obtain ⟨y, hy⟩ := p.coeff_support_nonempty
      exact ⟨y, hy, mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))⟩
  rw [expectation_const] at hlt
  exact (lt_irrefl _ hlt)

lemma expectation_distance_support_le [MetricSpace Y] (c p : FinProbability Y) :
    p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) ≤
      c.transport p := by
  have hc : c.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) = 0 := by
    apply expectation_eq_zero_of_support
    intro y hy
    exact Metric.infDist_zero_of_mem hy
  have hp : 0 ≤ p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) :=
    p.expectation_nonneg fun _ => Metric.infDist_nonneg
  have h := abs_gap_le_transport c p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
    (Metric.lipschitz_infDist_pt _)
  simpa only [gap, hc, zero_sub, abs_neg, abs_of_nonneg hp] using h

lemma exists_support_pair_dist_le [MetricSpace Y] (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support, dist a v ≤ c.transport p := by
  obtain ⟨v, hv, hvl⟩ := exists_support_le_expectation p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
  obtain ⟨a, ha, hva⟩ := c.coeff.support.finite_toSet.isCompact.exists_infDist_eq_dist
    (by simpa using c.coeff_support_nonempty) v
  refine ⟨a, ha, v, hv, ?_⟩
  rw [dist_comm, ← hva]
  exact hvl.trans (expectation_distance_support_le c p)

noncomputable def rho [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) : ℝ :=
  p.transport q / Real.sqrt (n : ℝ)

lemma rho_nonneg [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) :
    0 ≤ rho n p q := div_nonneg (transport_nonneg _ _) (Real.sqrt_nonneg _)

lemma rho_triangle [PseudoMetricSpace Y] (n : ℕ) (p q r : FinProbability Y) :
    rho n p r ≤ rho n p q + rho n q r := by
  unfold rho
  rw [← add_div]
  exact div_le_div_of_nonneg_right (transport_triangle p q r) (Real.sqrt_nonneg _)

lemma rho_comm [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) :
    rho n p q = rho n q p := by rw [rho, rho, transport_comm p q]

lemma sqrt_mul_rho [PseudoMetricSpace Y] {n : ℕ} (hn : 0 < n) (p q : FinProbability Y) :
    Real.sqrt (n : ℝ) * rho n p q = p.transport q := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  unfold rho
  field_simp

lemma coordinate_control_rho [MetricSpace Y] {n : ℕ} (hn : 0 < n)
    (p q : FinProbability Y) (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) (v : Y) :
    |p.coeff v - q.coeff v| ≤ Real.sqrt (n : ℝ) * rho n p q := by
  rw [sqrt_mul_rho hn]
  exact coordinate_control p q hdiscrete v

lemma support_distance_rho [MetricSpace Y] {n : ℕ} (hn : 0 < n)
    (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support,
      dist a v ≤ Real.sqrt (n : ℝ) * rho n c p := by
  rw [sqrt_mul_rho hn]
  exact exists_support_pair_dist_le c p

end FinProbability

end BassTrace.Sparse

end OAI
