import OAI.Topology.CoarseAssembly.RoeLocalCompactness
import Mathlib.Analysis.CStarAlgebra.Basic

namespace OAI

/-! # Local compactness of every operator in the reduced Roe algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open scoped ZeroAtInfty CStarAlgebra

variable {X H : Type*} [DecidableEq X] [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp

omit [DecidableEq X] [CompleteSpace H] in
theorem locallyCompact_zero : LocallyCompact (0 : Operator X H) := by
  intro f
  simp only [mul_zero, zero_mul]
  exact ⟨isCompactOperator_zero, isCompactOperator_zero⟩

omit [DecidableEq X] [CompleteSpace H] in
theorem LocallyCompact.add {T S : Operator X H} (hT : LocallyCompact T)
    (hS : LocallyCompact S) : LocallyCompact (T + S) := by
  intro f
  simp only [mul_add, add_mul]
  exact ⟨(hT f).1.add (hS f).1, (hT f).2.add (hS f).2⟩

omit [DecidableEq X] [CompleteSpace H] in
theorem LocallyCompact.mul {T S : Operator X H} (hT : LocallyCompact T)
    (hS : LocallyCompact S) : LocallyCompact (T * S) := by
  intro f
  constructor
  · rw [← mul_assoc]
    exact (hT f).1.comp_clm S
  · rw [mul_assoc]
    exact (hS f).2.clm_comp T

omit [DecidableEq X] [CompleteSpace H] in
theorem LocallyCompact.smul {T : Operator X H} (hT : LocallyCompact T) (z : ℂ) :
    LocallyCompact (z • T) := by
  intro f
  rw [mul_smul_comm, smul_mul_assoc]
  exact ⟨(hT f).1.smul z, (hT f).2.smul z⟩

omit [DecidableEq X] in
theorem locallyCompact_closed : IsClosed {T : Operator X H | LocallyCompact T} := by
  simp only [LocallyCompact, Set.ofPred_forall]
  apply isClosed_iInter
  intro f
  exact (isClosed_setOfPred_isCompactOperator.preimage (continuous_const.mul continuous_id)).inter
    (isClosed_setOfPred_isCompactOperator.preimage (continuous_id.mul continuous_const))

def locallyCompactAlgebra : NonUnitalStarSubalgebra ℂ (Operator X H) where
  carrier := {T | LocallyCompact T ∧ LocallyCompact (star T)}
  zero_mem' := by
    change LocallyCompact (0 : Operator X H) ∧ LocallyCompact (star (0 : Operator X H))
    rw [star_zero (Operator X H)]
    exact ⟨locallyCompact_zero, locallyCompact_zero⟩
  add_mem' hT hS := ⟨hT.1.add hS.1, by simpa only [star_add] using hT.2.add hS.2⟩
  mul_mem' hT hS := ⟨hT.1.mul hS.1, by simpa only [star_mul] using hS.2.mul hT.2⟩
  smul_mem' z T hT := ⟨hT.1.smul z, by simpa only [star_smul] using hT.2.smul (star z)⟩
  star_mem' hT := ⟨hT.2, by simpa only [star_star] using hT.1⟩

omit [DecidableEq X] [TopologicalSpace X] in
theorem operator_star_continuous : Continuous (fun T : Operator X H => star T) :=
  (ContinuousLinearMap.adjoint : Operator X H ≃ₗᵢ⋆[ℂ] Operator X H).continuous

omit [DecidableEq X] in
theorem locallyCompactAlgebra_closed :
    IsClosed (locallyCompactAlgebra (X := X) (H := H) : Set (Operator X H)) :=
  locallyCompact_closed.inter (locallyCompact_closed.preimage operator_star_continuous)

variable [PseudoMetricSpace X] [DiscreteTopology X]

theorem roe_locallyCompact
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} (hT : T ∈ algebra (X := X) (H := H)) : LocallyCompact T := by
  have hgen (S : Operator X H) (hS : Generator S) :
      S ∈ locallyCompactAlgebra (X := X) (H := H) := by
    refine ⟨generator_locallyCompact finiteBalls hS, ?_⟩
    obtain ⟨⟨r, _, hp⟩, _, hc⟩ := hS
    exact locallyCompact_of_propagation finiteBalls hp.star hc
  have hle : NonUnitalStarAlgebra.adjoin ℂ {S : Operator X H | Generator S} ≤
      locallyCompactAlgebra := NonUnitalStarAlgebra.adjoin_le hgen
  exact (NonUnitalStarSubalgebra.topologicalClosure_minimal _ hle locallyCompactAlgebra_closed hT).1

end CoarseAssembly.DiscreteRoe

end

end OAI
