import OAI.Topology.CoarseAssembly.Averaging
import OAI.Topology.CoarseAssembly.SpatialBlocks

namespace OAI

/-! # Spatial block projections

Adjoints commute with uniformly bounded Hilbert direct sums. Under the
explicit flattening equivalence, the sum of constant-fiber projections is
exactly the spatial projection `V V*` used by the Roe transfer.
-/

noncomputable section

namespace CoarseAssembly

open scoped Topology

variable {I : Type*} {E F : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, CompleteSpace (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
variable [∀ i, CompleteSpace (F i)]

theorem blockOperator_adjoint (A : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) :
    (blockOperator A C hC hA).adjoint =
      blockOperator (fun i => (A i).adjoint) C hC
        (fun i => (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _).trans_le (hA i)) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum, blockOperator_apply]
  exact tsum_congr (fun i => ContinuousLinearMap.adjoint_inner_left (A i) (y i) (x i))

omit [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)] in
theorem blockIsometry_toCLM (V : ∀ i, E i →ₗᵢ[ℂ] F i) :
    (blockIsometry V).toContinuousLinearMap =
      blockOperator (fun i => (V i).toContinuousLinearMap) 1 zero_le_one
        (fun i => (V i).norm_toContinuousLinearMap_le) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {Q : I → Type*} [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem block_constantProjection :
    blockOperator (fun i => constantProjection (H := H) (Q i)) 1 zero_le_one
      (fun i => constantProjection_norm_le (Q i)) =
    operatorConjugation (blockIsometry (fun i => fiberConstantIsometry (H := H) (Q i))) 1 := by
  rw [operatorConjugation, blockIsometry_toCLM, blockOperator_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  rfl

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_eq_conjugation
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator A = operatorConjugation
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry A := by
  let e := flattenEquiv (Q := Q) (H := H)
  have he : e.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.symm.toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.apply_symm_apply] using e.inner_map_map (e.symm x) y
  unfold flattenOperator operatorConjugation
  rw [he]

/-- Equality with the actual spatial projection, not merely agreement on
formal constant-fiber symbols. -/
theorem flatten_constantProjection :
    flattenOperator (Q := Q) (H := H) (blockOperator (fun i => constantProjection (H := H) (Q i))
      1 zero_le_one (fun i => constantProjection_norm_le (Q i))) =
      fiberProjection (H := H) Q := by
  rw [block_constantProjection (Q := Q) (H := H),
    flattenOperator_eq_conjugation, operatorConjugation_comp]
  rfl

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] [CompleteSpace H] in
theorem flattenOperator_sub
    (A B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator (A - B) = flattenOperator A - flattenOperator B := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext z
  rfl

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_mul
    (A B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) :
    flattenOperator (A * B) = flattenOperator A * flattenOperator B := by
  rw [flattenOperator_eq_conjugation, flattenOperator_eq_conjugation,
    flattenOperator_eq_conjugation, operatorConjugation_mul]

omit [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)] in
theorem flattenOperator_tendsto
    (A : ℕ → (lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2))
    (B : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2)
    (h : Filter.Tendsto A Filter.atTop (nhds B)) :
    Filter.Tendsto (fun n => flattenOperator (Q := Q) (H := H) (A n))
      Filter.atTop (nhds (flattenOperator B)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.mp h)
  rw [← flattenOperator_sub]
  exact flattenOperator_norm_le _

end CoarseAssembly

end

end OAI
