import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn

/-- The elementary Gibbs inequality in the exact finite form used for the
occupied-board product bound. No probability or overlap estimate is assumed. -/
lemma weighted_log_le {ι : Type*} (s : Finset ι) (p z : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hz : ∀ i ∈ s, 0 < z i) :
    ∑ i ∈ s, p i * Real.log (z i) ≤ ∑ i ∈ s, p i * (z i - 1) := by
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (hz i hi)) (hp i hi)

/-- Entropy of a distribution on k symbols is at most log k, including
zero probabilities. This is the marginal-entropy step in both grid proofs. -/
lemma entropy_le_log_card {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    -∑ i, p i * Real.log (p i) ≤ Real.log (Fintype.card ι) := by
  have hk : 0 < Fintype.card ι := by
    by_contra h
    have he : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by omega)
    have := hs
    simp at this
  have hkR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk
  have hb : ∀ i, -p i * Real.log (p i) - p i * Real.log (Fintype.card ι) ≤
      1 / Fintype.card ι - p i := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hpi' : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
      have hl := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (one_div_pos.mpr (mul_pos hkR hpi'))) (hp i)
      rw [Real.log_div (by norm_num) (mul_ne_zero (ne_of_gt hkR) hpi),
        Real.log_one, Real.log_mul (ne_of_gt hkR) hpi] at hl
      have he : p i * (1 / ((Fintype.card ι : ℝ) * p i) - 1) =
          1 / Fintype.card ι - p i := by field_simp
      rw [he] at hl
      nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hb i)
  simp only [neg_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib,
    hs, one_mul] at hsum
  have hc : ∑ _i : ι, 1 / (Fintype.card ι : ℝ) = 1 := by
    simp [div_eq_mul_inv, ne_of_gt hkR]
  rw [hc] at hsum
  linarith


/-- Marginal of the uniform distribution on `ι` along an actual line map. -/
def uniformMarginal {ι α : Type*} [Fintype ι] [DecidableEq α] (f : ι → α) (a : α) : ℝ :=
  ∑ i, if f i = a then (Fintype.card ι : ℝ)⁻¹ else 0

lemma uniformMarginal_nonneg {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f : ι → α) (a : α) : 0 ≤ uniformMarginal f a := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma sum_uniformMarginal_mul {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (f : ι → α) (g : α → ℝ) :
    ∑ a, uniformMarginal f a * g a = (Fintype.card ι : ℝ)⁻¹ * ∑ i, g (f i) := by
  simp only [uniformMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul]
  simp [← Finset.mul_sum]

lemma sum_uniformMarginal {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Nonempty ι] (f : ι → α) : ∑ a, uniformMarginal f a = 1 := by
  simpa using sum_uniformMarginal_mul f (fun _ => 1)

lemma uniformMarginal_pos {ι α : Type*} [Fintype ι] [DecidableEq α]
    [Nonempty ι] (f : ι → α) (i : ι) : 0 < uniformMarginal f (f i) := by
  have h := Finset.single_le_sum
    (f := fun j => if f j = f i then (Fintype.card ι : ℝ)⁻¹ else 0)
    (fun j (_ : j ∈ Finset.univ) => by split_ifs <;> positivity) (Finset.mem_univ i)
  simp only [ite_true] at h
  exact lt_of_lt_of_le (by positivity) h


lemma sum_over_embedding_le {ι α : Type*} [Fintype ι] [Fintype α]
    (e : ι ↪ α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ i, f (e i) ≤ ∑ a, f a := by
  rw [← Finset.sum_image (fun i _ j _ hij => e.injective hij)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => hf a)

/-- The exact exp(number of holes) product loss. The marginals are computed
from the actual occupied embedding, so arbitrary deletion patterns are covered.
This is the entropy/quarter-root normalization step of weighted.tex:143–150
and coherent.tex:191–205. -/
theorem occupied_product_of_mean_le {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : ι ↪ α × β) (z : α → β → ℝ) (hz : ∀ a b, 0 ≤ z a b)
    (hmean : ∑ a, ∑ b,
      uniformMarginal (fun i => (e i).1) a * uniformMarginal (fun i => (e i).2) b * z a b ≤ 1) :
    ∏ i, z (e i).1 (e i).2 ≤
      Real.exp ((Fintype.card α * Fintype.card β - Fintype.card ι : ℕ) : ℝ) := by
  classical
  by_cases hempty : IsEmpty ι
  · let := hempty
    simp only [Fintype.prod_empty]
    exact Real.one_le_exp (Nat.cast_nonneg _)
  have : Nonempty ι := not_isEmpty_iff.mp hempty
  by_cases hz0 : ∃ i, z (e i).1 (e i).2 = 0
  · obtain ⟨i, hi⟩ := hz0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    exact (Real.exp_pos _).le
  have hzpos : ∀ i, 0 < z (e i).1 (e i).2 := by
    intro i
    exact lt_of_le_of_ne (hz _ _) (Ne.symm (fun h => hz0 ⟨i, h⟩))
  let p := uniformMarginal (fun i => (e i).1)
  let q := uniformMarginal (fun i => (e i).2)
  let s : ℝ := Fintype.card ι
  have hs : 0 < s := by dsimp [s]; positivity
  have hp : ∀ i, 0 < p (e i).1 := uniformMarginal_pos _
  have hq : ∀ i, 0 < q (e i).2 := uniformMarginal_pos _
  have hps : ∑ a, p a = 1 := sum_uniformMarginal _
  have hqs : ∑ b, q b = 1 := sum_uniformMarginal _
  have hpe := entropy_le_log_card p (uniformMarginal_nonneg _) hps
  have hqe := entropy_le_log_card q (uniformMarginal_nonneg _) hqs
  have hmean' : ∑ i, p (e i).1 * q (e i).2 * z (e i).1 (e i).2 ≤ 1 := by
    apply (sum_over_embedding_le e (fun x => p x.1 * q x.2 * z x.1 x.2) ?_).trans
    · simpa only [Fintype.sum_prod_type] using hmean
    · intro x
      exact mul_nonneg (mul_nonneg (uniformMarginal_nonneg _ _) (uniformMarginal_nonneg _ _)) (hz _ _)
  have hlogs : ∑ i, Real.log (s * p (e i).1 * q (e i).2 * z (e i).1 (e i).2) ≤ 0 := by
    calc
      _ ≤ ∑ i, (s * (p (e i).1 * q (e i).2 * z (e i).1 (e i).2) - 1) := by
        apply Finset.sum_le_sum
        intro i _
        have hh := Real.log_le_sub_one_of_pos (mul_pos (mul_pos (mul_pos hs (hp i)) (hq i)) (hzpos i))
        simpa only [mul_assoc] using hh
      _ = s * (∑ i, p (e i).1 * q (e i).2 * z (e i).1 (e i).2) - s := by
        simp [Finset.sum_sub_distrib, ← Finset.mul_sum, s]
      _ ≤ 0 := by nlinarith
  have hlogexpand : ∑ i, Real.log (s * p (e i).1 * q (e i).2 * z (e i).1 (e i).2) =
      s * Real.log s + (∑ i, Real.log (p (e i).1)) + (∑ i, Real.log (q (e i).2)) +
        ∑ i, Real.log (z (e i).1 (e i).2) := by
    simp_rw [Real.log_mul (ne_of_gt (mul_pos (mul_pos hs (hp _)) (hq _))) (ne_of_gt (hzpos _)),
      Real.log_mul (ne_of_gt (mul_pos hs (hp _))) (ne_of_gt (hq _)),
      Real.log_mul (ne_of_gt hs) (ne_of_gt (hp _))]
    simp [Finset.sum_add_distrib, s]
  rw [hlogexpand] at hlogs
  have hplog : ∑ i, Real.log (p (e i).1) = s * ∑ a, p a * Real.log (p a) := by
    have h := sum_uniformMarginal_mul (fun i => (e i).1) (fun a => Real.log (p a))
    change _ = s⁻¹ * _ at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  have hqlog : ∑ i, Real.log (q (e i).2) = s * ∑ b, q b * Real.log (q b) := by
    have h := sum_uniformMarginal_mul (fun i => (e i).2) (fun b => Real.log (q b))
    change _ = s⁻¹ * _ at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  rw [hplog, hqlog] at hlogs
  have hlogbound : ∑ i, Real.log (z (e i).1 (e i).2) ≤
      s * (Real.log (Fintype.card α) + Real.log (Fintype.card β) - Real.log s) := by
    nlinarith [mul_le_mul_of_nonneg_left hpe hs.le, mul_le_mul_of_nonneg_left hqe hs.le]
  have hm : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨(e (Classical.choice inferInstance)).1⟩
    positivity
  have hn : (0 : ℝ) < Fintype.card β := by
    have : Nonempty β := ⟨(e (Classical.choice inferInstance)).2⟩
    positivity
  have hfrac := Real.log_le_sub_one_of_pos (div_pos (mul_pos hm hn) hs)
  rw [Real.log_div (ne_of_gt (mul_pos hm hn)) (ne_of_gt hs),
    Real.log_mul (ne_of_gt hm) (ne_of_gt hn)] at hfrac
  have hcancel : s * ((Fintype.card α : ℝ) * Fintype.card β / s - 1) =
      (Fintype.card α : ℝ) * Fintype.card β - s := by field_simp
  have hfinite : Fintype.card ι ≤ Fintype.card α * Fintype.card β := by
    simpa using Fintype.card_le_of_injective e e.injective
  have hfinal : ∑ i, Real.log (z (e i).1 (e i).2) ≤
      ((Fintype.card α * Fintype.card β - Fintype.card ι : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfinite, Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_left hfrac hs.le
    rw [hcancel] at h
    exact hlogbound.trans h
  calc
    _ = Real.exp (∑ i, Real.log (z (e i).1 (e i).2)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun i _ => (Real.exp_log (hzpos i)).symm)
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

end RowColumn

end
end

end OAI
