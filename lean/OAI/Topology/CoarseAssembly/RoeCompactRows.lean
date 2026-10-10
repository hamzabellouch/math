import OAI.Topology.CoarseAssembly.DiagonalMultiplier

namespace OAI

/-! # Compact rows and columns of locally compact finite-propagation operators -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finite_column_operator (T : Operator X H) (y : X) (s : Finset X)
    (hs : ∀ x, x ∉ s → entry T x y = 0) :
    T.comp (insert y) = ∑ x ∈ s, (insert x).comp (entry T x y) := by
  apply ContinuousLinearMap.ext
  intro h
  change T (insert y h) = _
  have hv : ∀ x, x ∉ s → T (insert y h) x = 0 := by
    intro x hx
    exact DFunLike.congr_fun (hs x hx) h
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, entry_apply, insert_apply] using
    vector_eq_sum s (T (insert y h)) hv

theorem finite_row_operator (T : Operator X H) (x : X) (s : Finset X)
    (hs : ∀ y, y ∉ s → entry T x y = 0) :
    (coordinate x).comp T = ∑ y ∈ s, (entry T x y).comp (coordinate y) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, coordinate_apply] using
    finite_row_apply T x s hs v

variable [PseudoMetricSpace X]

theorem compact_column_of_propagation
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} {r : ℝ} (hp : PropagationLE r T) (hc : CompactEntries T) (y : X) :
    IsCompactOperator (T.comp (insert y)) := by
  rw [finite_column_operator T y (finiteBalls y r).toFinset (column_support finiteBalls hp y)]
  apply (compactOperator (RingHom.id ℂ) H (Module X H)).sum_mem
  intro x _
  exact (hc x y).clm_comp (insert x)

theorem compact_row_of_propagation
    (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    {T : Operator X H} {r : ℝ} (hp : PropagationLE r T) (hc : CompactEntries T) (x : X) :
    IsCompactOperator ((coordinate x).comp T) := by
  have hs : ∀ y, y ∉ (finiteBalls x r).toFinset → entry T x y = 0 := by
    intro y hy
    apply hp
    simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall, not_le, dist_comm] using hy
  rw [finite_row_operator T x (finiteBalls x r).toFinset hs]
  apply (compactOperator (RingHom.id ℂ) (Module X H) H).sum_mem
  intro y _
  exact (hc x y).comp_clm (coordinate y)

omit [PseudoMetricSpace X] in
theorem finiteDiagonal_mul_compact (T : Operator X H)
    (hr : ∀ x, IsCompactOperator ((coordinate x).comp T)) (f : X → ℂ) (s : Finset X) :
    IsCompactOperator (finiteDiagonal (H := H) f s * T) := by
  unfold finiteDiagonal
  rw [Finset.sum_mul]
  apply (compactOperator (RingHom.id ℂ) (Module X H) (Module X H)).sum_mem
  intro x _
  exact ((hr x).clm_comp (insert x)).smul (f x)

omit [PseudoMetricSpace X] in
theorem mul_finiteDiagonal_compact (T : Operator X H)
    (hc : ∀ x, IsCompactOperator (T.comp (insert x))) (f : X → ℂ) (s : Finset X) :
    IsCompactOperator (T * finiteDiagonal (H := H) f s) := by
  unfold finiteDiagonal
  rw [Finset.mul_sum]
  apply (compactOperator (RingHom.id ℂ) (Module X H) (Module X H)).sum_mem
  intro x _
  have he : T * (f x • ((insert x).comp (coordinate x))) =
      f x • ((T.comp (insert x)).comp (coordinate x)) := by
    apply ContinuousLinearMap.ext
    intro v
    exact T.map_smul (f x) (insert x (coordinate x v))
  rw [he]
  exact ((hc x).comp_clm (coordinate x)).smul (f x)

end CoarseAssembly.DiscreteRoe

end

end OAI
