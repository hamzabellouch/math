import OAI.Topology.CoarseAssembly.FiniteHeadNormalization

namespace OAI

/-! # The whole-union boundary is unchanged by finitely many component changes -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopology H]

/-- Finite-head independence is proved within the single Roe algebra,
using controlled compact perturbations and equality of rational unitaries. -/
theorem separatedFamilyBoundary_eq_of_tail (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (J : Finset ℕ) (htail : ∀ i, i ∉ J → A i = B i) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let a := finiteHeadReplacement J A C hA r hp hAs hAsq
  let b := finiteHeadReplacement J B D hB s hq hBs hBsq
  have hC' : 0 ≤ max C 1 := zero_le_one.trans (le_max_right C 1)
  have hD' : 0 ≤ max D 1 := zero_le_one.trans (le_max_right D 1)
  have hr' : 0 ≤ max r (finiteHeadRadius (V := V) J) := hr.trans (le_max_left _ _)
  have hs' : 0 ≤ max s (finiteHeadRadius (V := V) J) := hs.trans (le_max_left _ _)
  have h1 := separatedFamilyBoundary_eq_of_component_compact o a.operator A (max C 1) C hC' hC a.norm_le hA
    (max r (finiteHeadRadius (V := V) J)) r hr' hr a.propagation hp a.selfAdjoint hAs (a.square_compact hAsq) hAsq a.compact_diff
  have h2 := separatedFamilyBoundary_eq_of_component_compact o b.operator B (max D 1) D hD' hD b.norm_le hB
    (max s (finiteHeadRadius (V := V) J)) s hs' hs b.propagation hq b.selfAdjoint hBs (b.square_compact hBsq) hBsq b.compact_diff
  have hm := separatedFamilyBoundary_eq_of_involutive_head o a.operator b.operator (max C 1) (max D 1)
    hC' hD' a.norm_le b.norm_le (max r (finiteHeadRadius (V := V) J))
    (max s (finiteHeadRadius (V := V) J)) hr' hs' a.propagation b.propagation a.selfAdjoint b.selfAdjoint (a.square_compact hAsq) (b.square_compact hBsq) J
    (fun i hi => (a.tail i hi).trans ((htail i hi).trans (b.tail i hi).symm)) a.involutive b.involutive
  exact h1.symm.trans (hm.trans h2)

end CoarseAssembly.DiscreteRoe

end

end OAI
