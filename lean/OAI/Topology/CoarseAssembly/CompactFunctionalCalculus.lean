import OAI.Topology.CoarseAssembly.CycleCompactPerturbation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

namespace OAI

/-! # Functional calculus preserves compact self-adjoint operators

Compact operators whose adjoints are compact form a closed star algebra.
The nonunital functional calculus stays in that algebra. This supplies the
compactness step in the remaining normalization of the odd coefficient.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def compactOperatorAlgebra (H : HilbertSpace) : NonUnitalStarSubalgebra ℂ (End H) where
  carrier := {T | IsCompactOperator T ∧ IsCompactOperator (star T : End H)}
  zero_mem' := by simp only [Set.mem_ofPred_eq, star_zero]; exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩
  add_mem' hT hS := by
    refine ⟨hT.1.add hS.1, ?_⟩
    rw [star_add]
    exact hT.2.add hS.2
  mul_mem' hT hS := by
    refine ⟨compact_mul_right hT.1 _, ?_⟩
    rw [star_mul]
    exact compact_mul_right hS.2 _
  smul_mem' z T hT := by
    refine ⟨hT.1.smul z, ?_⟩
    rw [star_smul]
    exact hT.2.smul (star z)
  star_mem' hT := by
    exact ⟨hT.2, by simpa only [star_star] using hT.1⟩

theorem compactOperatorAlgebra_closed : IsClosed (compactOperatorAlgebra H : Set (End H)) := by
  change IsClosed ({T : End H | IsCompactOperator T} ∩
    {T : End H | IsCompactOperator (star T : End H)})
  exact isClosed_setOfPred_isCompactOperator.inter
    (isClosed_setOfPred_isCompactOperator.preimage continuous_star)

theorem compact_cfcₙ (f : ℝ → ℝ) (T : End H)
    (hT : IsCompactOperator T) (hTs : IsCompactOperator (star T : End H)) :
    IsCompactOperator (cfcₙ f T : End H) := by
  let : IsClosed (compactOperatorAlgebra H : Set (End H)) := compactOperatorAlgebra_closed
  have ht : T ∈ compactOperatorAlgebra H := ⟨hT, hTs⟩
  exact (cfcₙ_mem (𝕜' := ℂ) (s := compactOperatorAlgebra H) f ht).1

theorem compact_cfc (f : ℝ → ℝ) (T : End H)
    (hT : IsCompactOperator T) (hTs : IsCompactOperator (star T : End H))
    (hf : ContinuousOn f (quasispectrum ℝ T)) (hf0 : f 0 = 0) :
    IsCompactOperator (cfc f T : End H) := by
  rw [← cfcₙ_eq_cfc hf hf0]
  exact compact_cfcₙ f T hT hTs

end CoarseAssembly.Analytic

end

end OAI
