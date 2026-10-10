import Mathlib.Analysis.CStarAlgebra.Spectrum
import OAI.Topology.CoarseAssembly.SigmaFunctionNorms
import OAI.Topology.CoarseAssembly.ProjectionBlocks

namespace OAI

/-! # Block representations of a countable compact family -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty CStarAlgebra

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
variable (c : ∀ j, OddCycle C(Y j, ℂ))

abbrev cycleHilbertFamily (j : ℕ) : HilbertSpace := (c j).space

theorem sigmaRepresentation_block_bound (f : C₀(Sigma Y, ℂ)) (j : ℕ) :
    ‖(c j).representation (sigmaFunctionRestriction Y j f)‖ ≤ ‖f‖ :=
  (NonUnitalStarAlgHom.norm_apply_le _ _).trans (sigmaFunctionRestriction_norm_le Y j f)

def sigmaRepresentationOperator (f : C₀(Sigma Y, ℂ)) :
    End (countableHilbertSpace (cycleHilbertFamily Y c)) :=
  CoarseAssembly.blockOperator (fun j => (c j).representation (sigmaFunctionRestriction Y j f))
    ‖f‖ (norm_nonneg f) (sigmaRepresentation_block_bound Y c f)

@[simp] theorem sigmaRepresentationOperator_apply (f : C₀(Sigma Y, ℂ))
    (x : HilbertSum (cycleHilbertFamily Y c)) (j : ℕ) :
    sigmaRepresentationOperator Y c f x j = (c j).representation (sigmaFunctionRestriction Y j f) (x j) := rfl

def sigmaCycleRepresentation : C₀(Sigma Y, ℂ) →⋆ₙₐ[ℂ]
    End (countableHilbertSpace (cycleHilbertFamily Y c)) where
  toFun := sigmaRepresentationOperator Y c
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j 0) (x j) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (f + g)) (x j) = _
    rw [map_add, map_add]
    rfl
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (f * g)) (x j) = _
    rw [map_mul, map_mul]
    rfl
  map_smul' z f := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (z • f)) (x j) = _
    rw [map_smul, map_smul]
    rfl
  map_star' f := by
    change sigmaRepresentationOperator Y c (star f) = (sigmaRepresentationOperator Y c f).adjoint
    rw [sigmaRepresentationOperator, sigmaRepresentationOperator, CoarseAssembly.blockOperator_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    change (c j).representation (sigmaFunctionRestriction Y j (star f)) (x j) = _
    rw [map_star, map_star]
    rfl

end CoarseAssembly.Analytic

end

end OAI
