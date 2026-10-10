import OAI.Topology.CoarseAssembly.Roe

namespace OAI

/-!
# Finite-propagation matrix calculus

The local-compactness step of the finite-fiber transfer states that
sandwiching a locally compact, finite-propagation operator by arbitrary
finite-propagation operators preserves local compactness. The multipliers
themselves are not assumed locally compact.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem insert_adjoint (x : X) : (insert (H := H) x).adjoint = coordinate x := by
  ext v
  apply ext_inner_left ℂ
  intro h
  simp [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_left]

theorem coordinate_adjoint (x : X) : (coordinate (H := H) x).adjoint = insert x := by
  rw [← insert_adjoint, ContinuousLinearMap.adjoint_adjoint]

theorem entry_star (T : Operator X H) (x y : X) :
    entry (star T) x y = star (entry T y x) := by
  simp [entry, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    insert_adjoint, coordinate_adjoint, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace H] in
theorem vector_eq_sum (s : Finset X) (v : Module X H)
    (hv : ∀ x, x ∉ s → v x = 0) :
    v = ∑ x ∈ s, insert x (v x) := by
  apply lp.ext
  funext x
  simp only [lp.coeFn_sum, Finset.sum_apply, insert_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx, hv x hx]

omit [CompleteSpace H] in
/-- Matrix multiplication is a finite sum whenever the right-hand column
has finite support. This avoids any exchange of infinite sums. -/
theorem entry_mul_of_finite_column (T S : Operator X H) (x y : X) (s : Finset X)
    (hs : ∀ z, z ∉ s → entry S z y = 0) :
    entry (T * S) x y = ∑ z ∈ s, entry T x z * entry S z y := by
  ext h
  have hv : S (insert y h) = ∑ z ∈ s, insert z (entry S z y h) := by
    apply vector_eq_sum
    intro z hz
    have := DFunLike.congr_fun (hs z hz) h
    simpa only [entry_apply, insert_apply, zero_apply] using this
  change coordinate x (T (S (insert y h))) = _
  rw [hv, map_sum, map_sum]
  simp only [sum_apply, mul_apply_eq_comp]
  rfl

variable [PseudoMetricSpace X]

theorem PropagationLE.star {r : ℝ} {T : Operator X H}
    (hT : PropagationLE r T) : PropagationLE r (star T) := by
  intro x y hxy
  rw [entry_star, hT y x (by simpa [dist_comm] using hxy), star_zero]

variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

omit [CompleteSpace H] in
theorem column_support {r : ℝ} {T : Operator X H} (hT : PropagationLE r T) (y : X) :
    ∀ z, z ∉ (finiteBalls y r).toFinset → entry T z y = 0 := by
  intro z hz
  apply hT
  simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall, not_le] using hz

omit [CompleteSpace H] in
include finiteBalls in
theorem PropagationLE.mul {r s : ℝ} {T S : Operator X H}
    (hT : PropagationLE r T) (hS : PropagationLE s S) :
    PropagationLE (r + s) (T * S) := by
  intro x y hxy
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hS y)]
  apply Finset.sum_eq_zero
  intro z hz
  have hzy : dist z y ≤ s := by
    simpa only [Set.Finite.mem_toFinset, Metric.mem_closedBall] using hz
  have hxz : r < dist x z := by
    have htri := dist_triangle x z y
    linarith
  rw [hT x z hxz, zero_mul]

omit [CompleteSpace H] in
theorem compact_sum {ι : Type*} (s : Finset ι) (A : ι → H →L[ℂ] H)
    (hA : ∀ i ∈ s, IsCompactOperator (A i)) :
    IsCompactOperator (∑ i ∈ s, A i : H →L[ℂ] H) := by
  exact (compactOperator (RingHom.id ℂ) H H).sum_mem hA

omit [CompleteSpace H] in
include finiteBalls in
theorem CompactEntries.mul_left {T S : Operator X H} {s : ℝ}
    (hT : CompactEntries T) (hS : PropagationLE s S) : CompactEntries (T * S) := by
  intro x y
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hS y)]
  apply compact_sum
  intro z _
  exact (hT x z).comp_clm (entry S z y)

omit [CompleteSpace H] in
include finiteBalls in
theorem CompactEntries.mul_right {T S : Operator X H} {s : ℝ}
    (hS : CompactEntries S) (hprop : PropagationLE s S) : CompactEntries (T * S) := by
  intro x y
  rw [entry_mul_of_finite_column T S x y (finiteBalls y s).toFinset
    (column_support finiteBalls hprop y)]
  apply compact_sum
  intro z _
  exact (hS z y).clm_comp (entry T x z)

include finiteBalls in
/-- Finite-propagation multipliers preserve locally compact generators.
In particular this applies to amplified finite-propagation projections,
without asserting that those projections are locally compact. -/
theorem generator_sandwich {A Q : Operator X H} {q : ℝ}
    (hA : Generator A) (hq : 0 ≤ q) (hQ : PropagationLE q Q) :
    Generator (Q * A * Q) := by
  obtain ⟨⟨a, ha, hprop⟩, hc, hcs⟩ := hA
  refine ⟨⟨(q + a) + q, by linarith,
    (hQ.mul finiteBalls hprop).mul finiteBalls hQ⟩, ?_, ?_⟩
  · exact (hc.mul_right finiteBalls hprop).mul_left finiteBalls hQ
  · rw [star_mul, star_mul, ← mul_assoc]
    exact (hcs.mul_right finiteBalls hprop.star).mul_left finiteBalls hQ.star

end CoarseAssembly.DiscreteRoe

end

end OAI
