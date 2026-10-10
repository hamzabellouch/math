import OAI.Topology.CoarseAssembly.SigmaCycleRepresentation

namespace OAI

/-! # Assembling uniformly bounded normalized Fredholm cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped ZeroAtInfty Topology

variable {H : HilbertSpace}

theorem norm_commutator_le (F T : End H) : ‖F * T - T * F‖ ≤ 2 * ‖F‖ * ‖T‖ := by
  calc
    _ ≤ ‖F * T‖ + ‖T * F‖ := norm_sub_le _ _
    _ ≤ ‖F‖ * ‖T‖ + ‖T‖ * ‖F‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

def sigmaCycleOperator : End (countableHilbertSpace (cycleHilbertFamily Y c)) :=
  CoarseAssembly.blockOperator (fun j => (c j).operator) M hM hF

theorem sigmaCycleOperator_selfAdjoint (hself : ∀ j, IsSelfAdjoint (c j).operator) :
    IsSelfAdjoint (sigmaCycleOperator Y c M hM hF) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr (fun j => (hself j).isSymmetric (x j) (y j))

theorem sigmaCycleOperator_sq (hsq : ∀ j, (c j).operator * (c j).operator = 1) :
    sigmaCycleOperator Y c M hM hF * sigmaCycleOperator Y c M hM hF = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  exact DFunLike.congr_fun (hsq j) (x j)

def sigmaCommutatorBlocks (f : C₀(Sigma Y, ℂ)) (j : ℕ) : End (c j).space :=
  (c j).operator * (c j).representation (sigmaFunctionRestriction Y j f) -
    (c j).representation (sigmaFunctionRestriction Y j f) * (c j).operator

include hM hF in
theorem sigmaCommutator_norm (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖sigmaCommutatorBlocks Y c f j‖ ≤ (2 * M) * ‖sigmaFunctionRestriction Y j f‖ := by
  apply (norm_commutator_le _ _).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hF j) (by norm_num))
    (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)
    (mul_nonneg (by norm_num) hM)

include hM hF in
theorem sigmaCommutator_uniform_bound (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖sigmaCommutatorBlocks Y c f j‖ ≤ (2 * M) * ‖f‖ :=
  (sigmaCommutator_norm Y c M hM hF f j).trans
    (mul_le_mul_of_nonneg_left (sigmaFunctionRestriction_norm_le Y j f) (by positivity))

include hM hF in
theorem sigmaCommutator_norm_tendsto (f : C₀(Sigma Y, ℂ)) :
    Tendsto (fun j => ‖sigmaCommutatorBlocks Y c f j‖) atTop (𝓝 0) := by
  have hb : Tendsto (fun j => (2 * M) * ‖sigmaFunctionRestriction Y j f‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (sigmaFunctionRestriction_norm_tendsto Y f)
  exact squeeze_zero (fun j => norm_nonneg _) (sigmaCommutator_norm Y c M hM hF f) hb

theorem sigmaCycleOperator_commutator (f : C₀(Sigma Y, ℂ)) :
    IsCompactOperator (sigmaCycleOperator Y c M hM hF * sigmaCycleRepresentation Y c f -
      sigmaCycleRepresentation Y c f * sigmaCycleOperator Y c M hM hF) := by
  have he : sigmaCycleOperator Y c M hM hF * sigmaCycleRepresentation Y c f -
      sigmaCycleRepresentation Y c f * sigmaCycleOperator Y c M hM hF =
      CoarseAssembly.blockOperator (sigmaCommutatorBlocks Y c f) ((2 * M) * ‖f‖)
        (by positivity) (sigmaCommutator_uniform_bound Y c M hM hF f) := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    rfl
  rw [he]
  exact blockSum_compact (cycleHilbertFamily Y c) (sigmaCommutatorBlocks Y c f)
    ((2 * M) * ‖f‖) (by positivity) (sigmaCommutator_uniform_bound Y c M hM hF f)
    (fun j => (c j).commutator_compact _) (sigmaCommutator_norm_tendsto Y c M hM hF f)

/-- A countable family of normalized cycles gives an actual locally finite cycle. -/
def sigmaCycle (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) : OddCycle C₀(Sigma Y, ℂ) where
  space := countableHilbertSpace (cycleHilbertFamily Y c)
  representation := sigmaCycleRepresentation Y c
  operator := sigmaCycleOperator Y c M hM hF
  commutator_compact := sigmaCycleOperator_commutator Y c M hM hF
  square_compact f := by
    rw [sigmaCycleOperator_sq Y c M hM hF hsq, sub_self, zero_mul]
    exact isCompactOperator_zero
  adjoint_compact f := by
    rw [(sigmaCycleOperator_selfAdjoint Y c M hM hF hself).star_eq, sub_self, zero_mul]
    exact isCompactOperator_zero

end CoarseAssembly.Analytic

end

end OAI
