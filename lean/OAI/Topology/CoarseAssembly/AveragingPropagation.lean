import OAI.Topology.CoarseAssembly.SpatialAveraging

namespace OAI

/-! # Finite propagation of the averaging powers

The left regular generators move at most one graph edge. The global lazy
average therefore has propagation one, and its powers have the expected
linear propagation bound on the actual separated union.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem translation_single_zero {Q : Type*} [Fintype Q] [Group Q]
    [DecidableEq Q] (g q r : Q) (hqr : q ≠ g * r) (v : H) :
    leftTranslation Q g (lp.single 2 r v) q = 0 := by
  change lp.single (E := fun _ : Q => H) 2 r v (g⁻¹ * q) = 0
  apply lp.single_apply_ne
  intro he
  apply hqr
  calc
    q = g * (g⁻¹ * q) := by group
    _ = g * r := by rw [he]

omit [CompleteSpace H] in
private theorem lazyAverage_single_zero (S : Finset ArithmeticGroup) (k : ℕ)
    (q r : Quotient k) (hqr : q ≠ r)
    (hm : ∀ s ∈ S, q ≠ reduce k s * r) (v : H) :
    lazyAverage S k (lp.single 2 r v) q = 0 := by
  classical
  simp only [lazyAverage, meanTranslation, smul_apply,
    add_apply, one_apply_eq_self,
    sum_apply, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sum,
    Pi.smul_apply, Pi.add_apply, Finset.sum_apply]
  change (1 / 2 : ℂ) •
    ((lp.single (E := fun _ : Quotient k => H) 2 r v) q + (S.card : ℂ)⁻¹ •
      ∑ s ∈ S, leftTranslation (H := H) (Quotient k) (reduce k s)
        (lp.single 2 r v) q) = 0
  rw [lp.single_apply_ne (E := fun _ : Quotient k => H) 2 r v hqr]
  have hz : ∑ s ∈ S, leftTranslation (H := H) (Quotient k) (reduce k s)
      (lp.single 2 r v) q = 0 := Finset.sum_eq_zero (fun s hs =>
        translation_single_zero (reduce k s) q r (hm s hs) v)
  rw [hz]
  simp

private theorem leftMove_distance (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (u : Disc j) (q : Quotient (discDepth j u))
    (s : ArithmeticGroup) (hs : s ∈ S) :
    @dist VertexUnion (vertexUnionMetric S t).toDist
      ⟨⟨j, u⟩, reduce (discDepth j u) s * q⟩ ⟨⟨j, u⟩, q⟩ ≤ 1 := by
  rw [vertexUnion_dist_same S t]
  by_cases he : reduce (discDepth j u) s * q = q
  · simp [he]
  · have ha : (fiberedGraph S t j).Adj ⟨u, q⟩ ⟨u, reduce (discDepth j u) s * q⟩ := by
      refine ⟨?_, s, ?_, Or.inl rfl, ?_⟩
      · intro h
        have hc : HEq q (reduce (discDepth j u) s * q) := (Sigma.mk.inj h).2
        exact he (eq_of_heq hc).symm
      · simp [symmetricMoves, hs]
      · intro m hq hr
        simp [fiberCoordinate, fiberCharge, latticeCharge_self, map_mul, quotientMap_reduce]
    have hd := SimpleGraph.dist_le ha.toWalk
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, zero_add] at hd
    rw [SimpleGraph.dist_comm]
    exact_mod_cast hd

def spatialLazyAverage (S : Finset ArithmeticGroup) : Operator VertexUnion H :=
  flattenOperator (Q := BaseFiber) (blockOperator
    (fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2))
    1 zero_le_one (fun _ => lazyAverage_norm_le S _))

theorem spatialLazyAverage_propagation (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    PropagationLE 1 (spatialLazyAverage (H := H) S) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro x y hdist
  apply ContinuousLinearMap.ext
  intro v
  rcases x with ⟨u, q⟩
  rcases y with ⟨w, r⟩
  change spatialLazyAverage S (lp.single 2 ⟨w, r⟩ v) ⟨u, q⟩ = 0
  by_cases huw : u = w
  · subst w
    change lazyAverage S (discDepth u.1 u.2)
      (rowVector (lp.single 2 ⟨u, r⟩ v) u) q = 0
    rw [rowVector_single_same]
    apply lazyAverage_single_zero
    · intro he
      subst q
      simp only [dist_self] at hdist
      exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1)) hdist
    · intro s hs he
      subst q
      exact (not_lt_of_ge (leftMove_distance S t u.2 r s hs)) hdist
  · change lazyAverage S (discDepth u.1 u.2)
      (rowVector (lp.single 2 ⟨w, r⟩ v) u) q = 0
    rw [rowVector_single_ne huw, map_zero]
    rfl

theorem spatialAveragingPower_eq_pow (S : Finset ArithmeticGroup) (n : ℕ) :
    spatialAveragingPower (H := H) S n = spatialLazyAverage S ^ (n + 1) := by
  let M := fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2)
  let A := fun n => blockOperator (fun u : BaseUnion => M u ^ (n + 1))
    1 zero_le_one (fiberAveragingPower_norm (H := H) S n)
  let B := blockOperator M 1 zero_le_one
    (fun u : BaseUnion => lazyAverage_norm_le (H := H) S (discDepth u.1 u.2))
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : A (n + 1) = A n * B := by
      apply ContinuousLinearMap.ext
      intro x
      apply lp.ext
      funext u
      change (M u ^ (n + 1 + 1)) (x u) = (M u ^ (n + 1)) (M u (x u))
      rw [pow_succ]
      rfl
    change flattenOperator (Q := BaseFiber) (A (n + 1)) = _
    rw [he, flattenOperator_mul]
    change spatialAveragingPower S n * spatialLazyAverage S = _
    rw [ih, ← pow_succ]

theorem spatialAveragingPower_propagation (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    ∀ n, PropagationLE (n + 1 : ℕ) (spatialAveragingPower (H := H) S n) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  have hfinite := (vertexUnion_uniform_balls S t).finite_closedBall
  have hM := spatialLazyAverage_propagation (H := H) S t
  intro n
  rw [spatialAveragingPower_eq_pow]
  induction n with
  | zero => simpa only [zero_add, pow_one, Nat.cast_one] using hM
  | succ n ih =>
    have hp := PropagationLE.mul hfinite ih hM
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one] using hp

/-- The concrete spatial transfer now requires only the published uniform
Kazhdan-gap specialization for these actual averages. -/
theorem concrete_transfer_of_gap (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (hS : S.Nonempty) (hgap : UniformAveragingGap S H) :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    MapsToRoe (fiberEmbedding (H := H) BaseFiber) := by
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  apply concrete_transfer_of_approximation S t (spatialAveragingPower S)
    (spatialAveragingPower_tendsto S hS hgap)
  intro n
  exact ⟨(n + 1 : ℕ), by positivity, spatialAveragingPower_propagation S t n⟩

end CoarseAssembly

end

end OAI
