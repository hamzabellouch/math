import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.DiagonalFamilyDefect
import OAI.Topology.CoarseAssembly.SeparatedRips
import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass
import OAI.Topology.CoarseAssembly.UnitalStructureAlgebra

namespace OAI

/-! # A Roe boundary class from a uniformly controlled separated family

The compact component defects need not decay in norm. Their direct sum is
nevertheless a finite-propagation operator with compact matrix entries,
which is the local compactness needed for the whole-union Roe algebra.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, DecidableEq (V i)] in
theorem separatedMetric_closedBall_finite (o : ∀ i, V i) (x : Sigma V) (r : ℝ) :
    letI := separatedMetric o
    (Metric.closedBall x r).Finite := by
  let := separatedMetric o
  simpa only [Metric.closedBall, dist_comm] using separated_closedBall_finite o x r

variable (o : ∀ i, V i) (A : ∀ i, Operator (V i) H)
  (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
  (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))

include o r hr hp in
theorem diagonalFamily_square_mem_roe (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    letI := separatedMetric o
    (diagonalFamily A C hC hA) ^ 2 - 1 ∈ algebra (X := Sigma V) (H := H) := by
  let := separatedMetric o
  have hT := diagonalFamily_propagation o A C hC hA r hp
  have hdef : PropagationLE (r + r) (diagonalFamily A C hC hA ^ 2 - 1) := by
    have hm := hT.mul (separatedMetric_closedBall_finite o) hT
    have hn := (propagationLE_one (X := Sigma V) (H := H)).smul (-1 : ℂ)
    have hh := hm.add hn
    have he : (-1 : ℂ) • (1 : Operator (Sigma V) H) = -(1 : Operator (Sigma V) H) := by
      ext v
      simp
    rw [he] at hh
    simpa only [pow_two, sub_eq_add_neg,
      max_eq_left (add_nonneg hr hr)] using hh
  have hc : CompactEntries (diagonalFamily A C hC hA ^ 2 - 1) := by
    simpa only [pow_two] using diagonalFamily_square_compactEntries A C hC hA hsq
  have hs : IsSelfAdjoint (diagonalFamily A C hC hA ^ 2 - 1) := by
    have hs' := (diagonalFamily_selfAdjoint A C hC hA hself).pow 2
    have hi : IsSelfAdjoint (1 : Operator (Sigma V) H) := IsSelfAdjoint.one _
    exact @IsSelfAdjoint.sub (Operator (Sigma V) H) inferInstance inferInstance _ _ hs' hi
  exact generator_mem ⟨⟨r + r, add_nonneg hr hr, hdef⟩, hc, by rwa [hs.star_eq]⟩

include o r hr hp in
theorem separatedFamilyMultiplier_selfAdjoint (hself : ∀ i, IsSelfAdjoint (A i)) :
    letI := separatedMetric o
    IsSelfAdjoint (separatedFamilyMultiplier o A C hC hA r hr hp) := by
  let := separatedMetric o
  apply Subtype.ext
  exact (diagonalFamily_selfAdjoint A C hC hA hself).star_eq

end CoarseAssembly.DiscreteRoe

end

end OAI
