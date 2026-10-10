import OAI.Topology.CoarseAssembly.BilateralShift
import OAI.Topology.CoarseAssembly.ToeplitzCompression

namespace OAI

/-! # The negative-frequency projection for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

private def negativeCoordinate (n : ℤ) : ℂ →L[ℂ] ℂ := if n < 0 then 1 else 0

private theorem negativeCoordinate_norm (n : ℤ) : ‖negativeCoordinate n‖ ≤ 1 := by
  unfold negativeCoordinate
  split_ifs
  · exact ContinuousLinearMap.norm_id_le
  · simp

def negativeProjection : End circleSequenceSpace :=
  CoarseAssembly.blockOperator negativeCoordinate 1 zero_le_one negativeCoordinate_norm

@[simp] theorem negativeProjection_apply (x : CircleSequence) (n : ℤ) :
    negativeProjection x n = if n < 0 then x n else 0 := by
  change (negativeCoordinate n) (x n) = _
  unfold negativeCoordinate
  split_ifs <;> rfl

theorem negativeProjection_sq : negativeProjection * negativeProjection = negativeProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change negativeProjection (negativeProjection x) n = negativeProjection x n
  rw [negativeProjection_apply (negativeProjection x) n, negativeProjection_apply x n]
  split_ifs <;> rfl

theorem negativeProjection_selfAdjoint : IsSelfAdjoint negativeProjection := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ (negativeProjection x n) (y n) = inner ℂ (x n) (negativeProjection y n)
  rw [negativeProjection_apply x n, negativeProjection_apply y n]
  split_ifs <;> simp

/-- The projection/shift commutator has exactly one nonzero row. -/
theorem negativeProjection_commutator (x : CircleSequence) :
    (negativeProjection * bilateralShift - bilateralShift * negativeProjection) x =
      -lp.single 2 0 (x (-1)) := by
  apply lp.ext
  funext n
  change negativeProjection (bilateralShift x) n - bilateralShift (negativeProjection x) n = _
  rw [negativeProjection_apply (bilateralShift x) n, bilateralShift_apply (negativeProjection x) n,
    negativeProjection_apply x (n - 1)]
  simp only [lp.coeFn_neg, Pi.neg_apply, lp.single_apply, Pi.single_apply]
  simp only [bilateralShift_apply x n]
  by_cases hzero : n = 0
  · subst n
    norm_num
  · have hsign : n - 1 < 0 ↔ n < 0 := by omega
    simp [hsign, hzero]


theorem negativeProjection_commutator_compact : IsCompactOperator
    (negativeProjection * bilateralShift - bilateralShift * negativeProjection) := by
  let ev : CircleSequence →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-1)
  let ins : ℂ →L[ℂ] CircleSequence := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0
  have he : negativeProjection * bilateralShift - bilateralShift * negativeProjection =
      -(ins ∘L ev) := by
    apply ContinuousLinearMap.ext
    intro x
    exact negativeProjection_commutator x
  rw [he]
  exact ((isCompactOperator_of_locallyCompactSpace_dom ev).clm_comp ins).neg

end CoarseAssembly.Analytic

end

end OAI
