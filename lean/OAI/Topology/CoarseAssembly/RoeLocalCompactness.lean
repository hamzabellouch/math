import OAI.Topology.CoarseAssembly.DiagonalApproximation

namespace OAI

/-! # Local compactness on the actual discrete ample module -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Filter
open scoped ZeroAtInfty Topology

variable {X H : Type*} [DecidableEq X] [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The usual local-compactness condition, with the actual multiplication operators. -/
def LocallyCompact (T : Operator X H) : Prop :=
  ∀ f : C₀(X, ℂ), IsCompactOperator (diagonalMultiplier (H := H) f * T) ∧
    IsCompactOperator (T * diagonalMultiplier (H := H) f)

variable [DiscreteTopology X] [CompleteSpace H]

theorem locallyCompact_of_compact_rows_columns (T : Operator X H)
    (hr : ∀ x, IsCompactOperator ((coordinate x).comp T))
    (hc : ∀ x, IsCompactOperator (T.comp (insert x))) : LocallyCompact T := by
  intro f
  constructor
  · apply isCompactOperator_of_tendsto (l := atTop)
      ((finiteDiagonal_tendsto (H := H) f).mul tendsto_const_nhds)
    exact Eventually.of_forall (fun s => finiteDiagonal_mul_compact T hr f s)
  · apply isCompactOperator_of_tendsto (l := atTop)
      (tendsto_const_nhds.mul (finiteDiagonal_tendsto (H := H) f))
    exact Eventually.of_forall (fun s => mul_finiteDiagonal_compact T hc f s)

variable [PseudoMetricSpace X]

theorem locallyCompact_of_propagation
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} {r : ℝ} (hp : PropagationLE r T) (hc : CompactEntries T) :
    LocallyCompact T :=
  locallyCompact_of_compact_rows_columns T
    (compact_row_of_propagation finiteBalls hp hc)
    (compact_column_of_propagation finiteBalls hp hc)

theorem generator_locallyCompact
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} (hT : Generator T) : LocallyCompact T := by
  obtain ⟨⟨r, _, hr⟩, hc, _⟩ := hT
  exact locallyCompact_of_propagation finiteBalls hr hc

end CoarseAssembly.DiscreteRoe

end

end OAI
