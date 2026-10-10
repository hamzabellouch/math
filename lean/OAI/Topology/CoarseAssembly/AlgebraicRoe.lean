import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RoeCalculus
import OAI.Topology.CoarseAssembly.LocallyCompactAlgebra

namespace OAI

/-! # The algebra of locally compact finite-propagation operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.instContinuousStarOperator

omit [CompleteSpace H] in
theorem PropagationLE.add {T S : Operator X H} {r s : ℝ}
    (hT : PropagationLE r T) (hS : PropagationLE s S) :
    PropagationLE (max r s) (T + S) := by
  intro x y hxy
  rw [entry_add, hT x y (lt_of_le_of_lt (le_max_left _ _) hxy),
    hS x y (lt_of_le_of_lt (le_max_right _ _) hxy), add_zero]

omit [CompleteSpace H] in
theorem PropagationLE.smul {T : Operator X H} {r : ℝ}
    (hT : PropagationLE r T) (z : ℂ) : PropagationLE r (z • T) := by
  intro x y hxy
  rw [entry_smul, hT x y hxy, smul_zero]

theorem Generator.zero : Generator (0 : Operator X H) := by
  refine ⟨⟨0, le_rfl, fun x y _ => entry_zero x y⟩, ?_, ?_⟩
  · intro x y
    rw [entry_zero]
    exact isCompactOperator_zero
  · rw [star_zero (Operator X H)]
    intro x y
    rw [entry_zero]
    exact isCompactOperator_zero

theorem Generator.add {T S : Operator X H} (hT : Generator T) (hS : Generator S) :
    Generator (T + S) := by
  obtain ⟨⟨r, hr, hp⟩, hc, hcs⟩ := hT
  obtain ⟨⟨s, hs, hq⟩, hd, hds⟩ := hS
  refine ⟨⟨max r s, le_trans hr (le_max_left _ _), hp.add hq⟩, ?_, ?_⟩
  · intro x y
    rw [entry_add]
    exact (hc x y).add (hd x y)
  · rw [star_add T S]
    intro x y
    rw [entry_add]
    exact (hcs x y).add (hds x y)

theorem Generator.smul {T : Operator X H} (hT : Generator T) (z : ℂ) : Generator (z • T) := by
  obtain ⟨⟨r, hr, hp⟩, hc, hcs⟩ := hT
  refine ⟨⟨r, hr, hp.smul z⟩, ?_, ?_⟩
  · intro x y
    rw [entry_smul]
    exact (hc x y).smul z
  · rw [star_smul]
    intro x y
    rw [entry_smul]
    exact (hcs x y).smul (star z)

theorem Generator.star {T : Operator X H} (hT : Generator T) : Generator (star T) := by
  obtain ⟨⟨r, hr, hp⟩, hc, hcs⟩ := hT
  exact ⟨⟨r, hr, hp.star⟩, hcs, by simpa only [star_star] using hc⟩

theorem Generator.mul (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T S : Operator X H} (hT : Generator T) (hS : Generator S) : Generator (T * S) := by
  obtain ⟨⟨r, hr, hp⟩, hc, hcs⟩ := hT
  obtain ⟨⟨s, hs, hq⟩, hd, hds⟩ := hS
  exact ⟨⟨r + s, add_nonneg hr hs, hp.mul finiteBalls hq⟩,
    hc.mul_left finiteBalls hq, by
      rw [star_mul]
      exact hds.mul_left finiteBalls hp.star⟩

theorem roe_eq_closure_algebraic
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite) :
    algebra (X := X) (H := H) = (algebraicRoe (H := H) finiteBalls).topologicalClosure := by
  have he : NonUnitalStarAlgebra.adjoin ℂ {T : Operator X H | Generator T} =
      algebraicRoe (H := H) finiteBalls := by
    apply le_antisymm
    · exact NonUnitalStarAlgebra.adjoin_le (fun _ h => h)
    · intro T hT
      exact NonUnitalStarAlgebra.subset_adjoin ℂ _ hT
  unfold algebra
  rw [he]

end CoarseAssembly.DiscreteRoe

end

end OAI
