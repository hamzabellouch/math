import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.AlgebraicRoe
import OAI.Topology.CoarseAssembly.PseudolocalAlgebra

namespace OAI

/-! # Multiplication of the Roe ideal by controlled pseudolocal operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instContinuousStarOperator_1

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instIsScalarTowerComplexOperator_2

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instSMulCommClassComplexOperator_2

theorem finitePropagation_multiplier
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} {r : ℝ} (hr : 0 ≤ r) (hp : PropagationLE r T) : RoeMultiplier T := by
  have hprod (S : Operator X H) (hS : Generator S) :
      T * S ∈ algebra (X := X) (H := H) ∧ S * T ∈ algebra (X := X) (H := H) := by
    obtain ⟨⟨s, hs, hq⟩, hc, hcs⟩ := hS
    constructor
    · apply generator_mem
      refine ⟨⟨r + s, add_nonneg hr hs, hp.mul finiteBalls hq⟩,
        hc.mul_right finiteBalls hq, ?_⟩
      rw [star_mul]
      exact hcs.mul_left finiteBalls hp.star
    · apply generator_mem
      refine ⟨⟨s + r, add_nonneg hs hr, hq.mul finiteBalls hp⟩,
        hc.mul_left finiteBalls hp, ?_⟩
      rw [star_mul]
      exact hcs.mul_right finiteBalls hq.star
  have hclosed : IsClosed {S : Operator X H |
      T * S ∈ algebra (X := X) (H := H) ∧ S * T ∈ algebra (X := X) (H := H)} :=
    (algebra_isClosed.preimage (continuous_const.mul continuous_id)).inter
      (algebra_isClosed.preimage (continuous_id.mul continuous_const))
  intro S
  have hm : S.val ∈ (algebraicRoe (H := H) finiteBalls).topologicalClosure := by
    rw [← roe_eq_closure_algebraic finiteBalls]
    exact S.property
  exact closure_minimal hprod hclosed hm

theorem roeIdealizer_closed : IsClosed (roeIdealizer (X := X) (H := H) : Set (Operator X H)) := by
  simp only [roeIdealizer, RoeMultiplier, Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  exact (algebra_isClosed.preimage (continuous_id.mul continuous_const)).inter
    (algebra_isClosed.preimage (continuous_const.mul continuous_id))

theorem structureAlgebra_multiplier
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} (hT : T ∈ structureAlgebra (X := X) (H := H)) : RoeMultiplier T := by
  have hle : NonUnitalStarAlgebra.adjoin ℂ {S : Operator X H | StructureGenerator S} ≤
      roeIdealizer := by
    apply NonUnitalStarAlgebra.adjoin_le
    intro S hS
    obtain ⟨r, hr, hp⟩ := hS.1
    exact finitePropagation_multiplier finiteBalls hr hp
  exact NonUnitalStarSubalgebra.topologicalClosure_minimal _ hle roeIdealizer_closed hT

end CoarseAssembly.DiscreteRoe

end

end OAI
