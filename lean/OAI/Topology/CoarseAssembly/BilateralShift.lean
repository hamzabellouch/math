import OAI.Topology.CoarseAssembly.HilbertSum
import OAI.Topology.CoarseAssembly.FredholmModule

namespace OAI

/-! # The separable Hilbert space and bilateral shift for the circle cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

abbrev CircleSequence := lp (fun _ : ℤ => ℂ) 2

instance circleSequence_secondCountable : SecondCountableTopology CircleSequence := by
  let b : HilbertBasis ℤ ℂ CircleSequence := default
  have hs := ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℂ (Set.range b)).topologicalClosure : Set CircleSequence) at hs
  rw [b.dense_span] at hs
  have : SeparableSpace CircleSequence := TopologicalSpace.isSeparable_univ_iff.mp hs
  infer_instance

abbrev circleSequenceSpace : HilbertSpace where
  Carrier := CircleSequence
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

/-- Reindex square-summable integer sequences by a permutation. -/
def reindexSequence (e : ℤ ≃ ℤ) (x : CircleSequence) : CircleSequence :=
  ⟨fun n => x (e.symm n), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact e.symm.summable_iff.mpr (CoarseAssembly.l2_summable_sq x)⟩

theorem reindexSequence_norm (e : ℤ ≃ ℤ) (x : CircleSequence) : ‖reindexSequence e x‖ = ‖x‖ := by
  have he : ‖reindexSequence e x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [CoarseAssembly.l2_norm_sq, CoarseAssembly.l2_norm_sq]
    exact e.symm.tsum_eq (fun n => ‖x n‖ ^ 2)
  nlinarith [norm_nonneg x, norm_nonneg (reindexSequence e x)]

def reindexSequenceEquiv (e : ℤ ≃ ℤ) : CircleSequence ≃ₗᵢ[ℂ] CircleSequence where
  toFun := reindexSequence e
  invFun := reindexSequence e.symm
  left_inv x := by apply lp.ext; funext n; simp [reindexSequence]
  right_inv x := by apply lp.ext; funext n; simp [reindexSequence]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := reindexSequence_norm e

/-- The shift sends the basis vector at `n` to the basis vector at `n+1`. -/
def bilateralShiftEquiv : CircleSequence ≃ₗᵢ[ℂ] CircleSequence :=
  reindexSequenceEquiv (Equiv.addRight 1)

def bilateralShift : End circleSequenceSpace := (bilateralShiftEquiv : CircleSequence →L[ℂ] CircleSequence)

@[simp] theorem bilateralShift_apply (x : CircleSequence) (n : ℤ) :
    bilateralShift x n = x (n - 1) := rfl

theorem bilateralShift_unitary : star bilateralShift * bilateralShift = 1 ∧
    bilateralShift * star bilateralShift = 1 := by
  have hs : star bilateralShift = (bilateralShiftEquiv.symm : CircleSequence →L[ℂ] CircleSequence) :=
    bilateralShiftEquiv.adjoint_eq_symm
  rw [hs]
  constructor <;> apply ContinuousLinearMap.ext <;> intro x
  · exact bilateralShiftEquiv.symm_apply_apply x
  · exact bilateralShiftEquiv.apply_symm_apply x

end CoarseAssembly.Analytic

end

end OAI
