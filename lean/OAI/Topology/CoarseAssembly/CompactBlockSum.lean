import OAI.Topology.CoarseAssembly.CountableHilbertSum
import OAI.Topology.CoarseAssembly.CycleCompactPerturbation

namespace OAI

/-! # Compact diagonal operators on a countable Hilbert sum -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped Topology

variable (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))

def singleBlock (j : ℕ) : End (countableHilbertSpace H) :=
  (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j) ∘L K j ∘L
    lp.evalCLM ℂ (fun j => H j) 2 j

theorem singleBlock_compact (j : ℕ) (hK : IsCompactOperator (K j)) :
    IsCompactOperator (singleBlock H K j) :=
  (hK.comp_clm (lp.evalCLM ℂ (fun j => H j) 2 j)).clm_comp
    (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j)

def truncateBlocks (N j : ℕ) : End (H j) := if j < N then K j else 0

theorem truncateBlocks_norm (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    ∀ j, ‖truncateBlocks H K N j‖ ≤ C := by
  intro j
  unfold truncateBlocks
  split_ifs
  · exact hK j
  · simpa only [norm_zero] using hC

def truncatedBlockSum (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    End (countableHilbertSpace H) :=
  CoarseAssembly.blockOperator (truncateBlocks H K N) C hC (truncateBlocks_norm H K N C hC hK)

theorem truncatedBlockSum_apply (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (x : HilbertSum H) (j : ℕ) :
    truncatedBlockSum H K N C hC hK x j = if j < N then K j (x j) else 0 := by
  change (truncateBlocks H K N j) (x j) = _
  unfold truncateBlocks
  split_ifs <;> rfl

theorem truncatedBlockSum_succ (N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C) :
    truncatedBlockSum H K (N + 1) C hC hK =
      truncatedBlockSum H K N C hC hK + singleBlock H K N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change truncatedBlockSum H K (N + 1) C hC hK x j =
    truncatedBlockSum H K N C hC hK x j + (lp.single (E := fun j => H j) 2 N (K N (x N))) j
  rw [truncatedBlockSum_apply H K (N + 1) C hC hK x j,
    truncatedBlockSum_apply H K N C hC hK x j]
  by_cases hj : j = N
  · subst j
    simp only [Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false,
      lp.single_apply_self, zero_add]
  · have hlt : j < N + 1 ↔ j < N := by omega
    rw [lp.single_apply_ne (E := fun j => H j) 2 N (K N (x N)) hj, add_zero]
    simp only [hlt]

theorem truncatedBlockSum_compact (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (hc : ∀ j, IsCompactOperator (K j)) (N : ℕ) :
    IsCompactOperator (truncatedBlockSum H K N C hC hK) := by
  induction N with
  | zero =>
    have he : truncatedBlockSum H K 0 C hC hK = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext j
      rw [truncatedBlockSum_apply H K 0 C hC hK x j]
      simp
    rw [he]
    exact isCompactOperator_zero
  | succ N ih =>
    rw [truncatedBlockSum_succ]
    exact ih.add (singleBlock_compact H K N (hc N))

theorem blockSum_compact (C : ℝ) (hC : 0 ≤ C) (hK : ∀ j, ‖K j‖ ≤ C)
    (hc : ∀ j, IsCompactOperator (K j)) (htail : Tendsto (fun j => ‖K j‖) atTop (𝓝 0)) :
    IsCompactOperator (CoarseAssembly.blockOperator K C hC hK) := by
  apply isCompactOperator_of_tendsto (l := atTop) (F := fun N => truncatedBlockSum H K N C hC hK)
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (CoarseAssembly.blockOperator_dist_le _ _ C C (ε / 2) hC hC
      (by positivity) (truncateBlocks_norm H K n C hC hK) hK ?_) (by linarith)
    intro j
    unfold truncateBlocks
    split_ifs with hj
    · simp only [sub_self, norm_zero]
      positivity
    · simp only [zero_sub, norm_neg]
      have hjn : N ≤ j := hn.trans (Nat.le_of_not_gt hj)
      have hsmall := hN j hjn
      simpa only [dist_zero_right, norm_norm] using le_of_lt hsmall
  · exact Filter.Eventually.of_forall (truncatedBlockSum_compact H K C hC hK hc)

end CoarseAssembly.Analytic

end

end OAI
