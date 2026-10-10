import OAI.RepresentationTheory.Saxl.DominatedSupport

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
inductive StripChain : ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : StripChain 0 μ μ
  | snoc {q ν η μ} : StripChain q ν η → HorizontalStrip η μ → η ≠ μ → StripChain (q+1) ν μ


lemma stripRemove_full_prefix (μ : YoungDiagram) (q : ℕ) :
    rowPrefix (stripRemove μ (μ.rowLen 0)) q + μ.rowLen 0 = rowPrefix μ (q+1) := by
  have hh := stripRemove_prefix μ (μ.rowLen 0) q
  rw [min_self, min_eq_right (μ.rowLen_anti 0 q (Nat.zero_le _))] at hh
  exact hh.trans (rowPrefix_succ μ q).symm

/- Sweeps remove any prescribed number within the first q-row capacity. -/
theorem stripChain_of_capacity (q t : ℕ) (μ : YoungDiagram)
    (ht : t ≤ rowPrefix μ q) :
    ∃ k ≤ q, ∃ ν, ν.card + t = μ.card ∧ StripChain k ν μ := by
  induction q generalizing t μ with
  | zero =>
    have hz : t = 0 := by simpa [rowPrefix] using ht
    exact ⟨0, le_rfl, μ, by omega, StripChain.nil μ⟩
  | succ q ih =>
    by_cases hz : t = 0
    · exact ⟨0, Nat.zero_le _, μ, by omega, StripChain.nil μ⟩
    by_cases hb : t ≤ μ.rowLen 0
    · let ν := stripRemove μ t
      have hc : ν.card + t = μ.card := by
        simpa only [ν, min_eq_left hb] using stripRemove_card μ t
      have hn : ν ≠ μ := by intro he; rw [he] at hc; omega
      exact ⟨1, by omega, ν, hc,
        StripChain.snoc (StripChain.nil ν) (stripRemove_horizontal μ t) hn⟩
    · let η := stripRemove μ (μ.rowLen 0)
      have hp : rowPrefix η q + μ.rowLen 0 = rowPrefix μ (q+1) :=
        stripRemove_full_prefix μ q
      have hcap : t - μ.rowLen 0 ≤ rowPrefix η q := by omega
      obtain ⟨k, hk, ν, hc, hchain⟩ := ih (t-μ.rowLen 0) η hcap
      have hec : η.card + μ.rowLen 0 = μ.card := by
        simpa only [η, min_self] using stripRemove_card μ (μ.rowLen 0)
      have hpos : 0 < μ.rowLen 0 := by
        by_contra h
        have hz0 : μ.rowLen 0 = 0 := by omega
        have hp0 : rowPrefix μ (q+1) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
          omega
        omega
      have hn : η ≠ μ := by intro he; rw [he] at hec; omega
      refine ⟨k+1, by omega, ν, ?_, StripChain.snoc hchain (stripRemove_horizontal μ _) hn⟩
      omega

lemma rowPrefix_mean (μ : YoungDiagram) {q k : ℕ} (hqk : q ≤ k) :
    q * rowPrefix μ k ≤ k * rowPrefix μ q := by
  have hlow : q * μ.rowLen q ≤ rowPrefix μ q := by
    calc
      q * μ.rowLen q = ∑ i ∈ Finset.range q, μ.rowLen q := by simp
      _ ≤ rowPrefix μ q := Finset.sum_le_sum (fun i hi =>
        μ.rowLen_anti i q (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have he : rowPrefix μ k = rowPrefix μ q +
      ∑ i ∈ Finset.range (k-q), μ.rowLen (q+i) := by
    simp only [rowPrefix]
    rw [← Finset.sum_range_add]
    congr 2
    omega
  have htail : (∑ i ∈ Finset.range (k-q), μ.rowLen (q+i)) ≤ (k-q)*μ.rowLen q := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k-q), μ.rowLen q :=
        Finset.sum_le_sum (fun i hi => μ.rowLen_anti q (q+i) (by omega))
      _ = _ := by simp
  have hm := Nat.mul_le_mul_left (k-q) hlow
  have hs := Nat.mul_le_mul_left q htail
  rw [he]
  have hsum : q + (k-q) = k := by omega
  nlinarith

@[simp] lemma staircase_rowLen (m i : ℕ) : (staircase m).rowLen i = m-i := by
  have hh : ∀ j, j < (staircase m).rowLen i ↔ j < m-i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).rowLen i)
  have h₂ := hh (m-i)
  omega

lemma staircase_prefix_double (m k : ℕ) (hk : k ≤ m) :
    2 * rowPrefix (staircase m) k = k * (2*m+1-k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ, staircase_rowLen]
    have hi := ih (by omega)
    have hs : k + (m-k) = m := by omega
    have ht : k + (2*m+1-k) = 2*m+1 := by omega
    have ht' : (k+1) + (2*m+1-(k+1)) = 2*m+1 := by omega
    nlinarith

/- The exact capacity alternative used by the main induction. -/
lemma strip_reduction_capacity (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ)
    (hfirst : μ.rowLen 0 < m) : 5 ≤ m ∧ 2*m-1 ≤ rowPrefix μ 4 := by
  obtain ⟨k, hk⟩ : ∃ k, rowPrefix (staircase m) k < rowPrefix μ k := by
    simpa only [Dominates, not_forall, not_le] using hdom
  have hkm : k < m := by
    by_contra hh
    have hc : (staircase m).colLen 0 ≤ k := by simp; omega
    rw [rowPrefix_eq_card _ hc] at hk
    have hle := rowPrefix_le_card μ k
    omega
  have hbound : rowPrefix μ k ≤ k * (m-1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (m-1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
        omega
      _ = _ := by simp
  have hstair := staircase_prefix_double m k (by omega)
  have hk4 : 4 ≤ k := by
    have hm1 : m = (m-1)+1 := by omega
    by_contra hh
    interval_cases k <;> omega
  have hmean := rowPrefix_mean μ hk4
  have hpos : 0 < k := by omega
  have hsum : k + (2*m+1-k) = 2*m+1 := by omega
  constructor
  · omega
  · have ha : 4*(2*m+1-k) < 2*rowPrefix μ 4 := by
      nlinarith
    have hb : 2*m-1 ≤ 2*(2*m+1-k) := by omega
    omega

theorem strip_reduction (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ) :
    (∃ ν, ν.card = (staircase (m-1)).card ∧ HorizontalStrip ν μ) ∨
    (5 ≤ m ∧ ∃ q ≤ 4, ∃ ν, ν.card = (staircase (m-2)).card ∧ StripChain q ν μ) := by
  by_cases hfirst : m ≤ μ.rowLen 0
  · left
    let ν := stripRemove μ m
    have hc : ν.card + m = μ.card := by
      simpa only [ν, min_eq_left hfirst] using stripRemove_card μ m
    have hs : (staircase m).card = (staircase (m-1)).card + m := by
      have hh := staircase_card_succ (m-1)
      have he : m-1+1 = m := by omega
      simpa only [he] using hh
    exact ⟨ν, by omega, stripRemove_horizontal μ m⟩
  · right
    obtain ⟨hm5, hcap⟩ := strip_reduction_capacity m hm μ hμ hdom (by omega)
    obtain ⟨q, hq, ν, hc, hs⟩ := stripChain_of_capacity 4 (2*m-1) μ hcap
    refine ⟨hm5, q, hq, ν, ?_, hs⟩
    have hc₁ := staircase_card_double m
    have hc₂ := staircase_card_double (m-2)
    have hh : m = (m-2)+2 := by omega
    have ht : 2*m-1+1 = 2*m := by omega
    nlinarith

end Saxl

end

end OAI
