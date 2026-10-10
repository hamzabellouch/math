import OAI.Topology.CoarseAssembly.CycleCompactPerturbation
import Mathlib.Tactic.Module

namespace OAI

/-! # Self-adjoint normalization of a unital Fredholm cycle

The compact adjoint defect allows replacement of the operator by its
self-adjoint part, with the represented algebra and K-homology class fixed.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem exists_selfAdjoint_representative (c : OddCycle A)
    (hunital : c.representation 1 = 1) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧
      d.representation 1 = 1 ∧ IsSelfAdjoint d.operator := by
  let K : End c.space := (1 / 2 : ℝ) • (star c.operator - c.operator)
  have hdefect : IsCompactOperator (star c.operator - c.operator : End c.space) := by
    simpa only [hunital, mul_one] using c.adjoint_compact 1
  have hK : IsCompactOperator K := hdefect.smul (1 / 2 : ℝ)
  have hstar : star K = -K := by
    dsimp only [K]
    rw [star_smul, star_trivial, star_sub, star_star]
    module
  have hKs : IsCompactOperator (star K : End c.space) := by
    rw [hstar]
    exact hK.neg
  refine ⟨c.compactPerturb K hK hKs, compactPerturb_class c K hK hKs, hunital, ?_⟩
  change star (c.operator + K) = c.operator + K
  rw [star_add, hstar]
  dsimp only [K]
  module

end CoarseAssembly.Analytic

end

end OAI
