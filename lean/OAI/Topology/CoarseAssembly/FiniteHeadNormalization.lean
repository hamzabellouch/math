import OAI.Topology.CoarseAssembly.FiniteHeadBoundary
import OAI.Topology.CoarseAssembly.UniformCycleNormalization
import Mathlib.Analysis.Normed.Lp.LpEquiv

namespace OAI

/-! # Uniformly controlled involutive replacement of a finite head -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteHeadRadius (J : Finset ℕ) : ℝ := ∑ i ∈ J, ∑ x : V i, ∑ y : V i, dist x y

omit [∀ i, DecidableEq (V i)] in
theorem finiteHeadRadius_nonneg (J : Finset ℕ) : 0 ≤ finiteHeadRadius (V := V) J :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg)))

omit [∀ i, DecidableEq (V i)] in
theorem finiteHeadRadius_diam (J : Finset ℕ) {i : ℕ} (hi : i ∈ J) (x y : V i) :
    dist x y ≤ finiteHeadRadius (V := V) J := by
  have h1 : dist x y ≤ ∑ z : V i, dist x z :=
    Finset.single_le_sum (f := fun z : V i => dist x z) (fun _ _ => dist_nonneg) (Finset.mem_univ y)
  have h2 : (∑ z : V i, dist x z) ≤ ∑ z : V i, ∑ w : V i, dist z w :=
    Finset.single_le_sum (f := fun z : V i => ∑ w : V i, dist z w)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Finset.mem_univ x)
  have h3 : (∑ z : V i, ∑ w : V i, dist z w) ≤ finiteHeadRadius (V := V) J :=
    Finset.single_le_sum (f := fun j => ∑ z : V j, ∑ w : V j, dist z w)
      (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg))) hi
  exact h1.trans (h2.trans h3)

omit [CompleteSpace H] in
theorem finiteHead_propagation (J : Finset ℕ) (A B : ∀ i, Operator (V i) H)
    (r : ℝ) (hp : ∀ i, PropagationLE r (A i)) (htail : ∀ i, i ∉ J → B i = A i) :
    ∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (B i) := by
  intro i x y hxy
  by_cases hi : i ∈ J
  · exact False.elim ((not_lt_of_ge ((finiteHeadRadius_diam J hi x y).trans (le_max_right _ _))) hxy)
  · rw [htail i hi]
    exact hp i x y ((le_max_left _ _).trans_lt hxy)

variable [SecondCountableTopology H]

def componentHilbert (i : ℕ) : HilbertSpace where
  Carrier := Module (V i) H
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := (lpPiLpₗᵢ (fun _ : V i => H) ℂ (p := 2)).isometry.isEmbedding.secondCountableTopology

/-- Only finitely many components are changed. Their new operators are
involutions, their differences are compact, and all propagation stays bounded. -/
theorem exists_finiteHead_involution (J : Finset ℕ) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i))
    (hs : ∀ i, IsSelfAdjoint (A i))
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    ∃ B : ∀ i, Operator (V i) H,
      (∀ i, IsSelfAdjoint (B i)) ∧
      (∀ i, ‖B i‖ ≤ max C 1) ∧
      (∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (B i)) ∧
      (∀ i, IsCompactOperator (B i - A i)) ∧
      (∀ i, i ∈ J → B i * B i = 1) ∧
      (∀ i, i ∉ J → B i = A i) := by
  have hex (i : ℕ) : ∃ N : Operator (V i) H,
      IsSelfAdjoint N ∧ N * N = 1 ∧ IsCompactOperator (N - A i : Operator (V i) H) ∧
        IsCompactOperator (star (N - A i) : Operator (V i) H) :=
    @exists_compact_involution (componentHilbert (V := V) (H := H) i) (A i) (hs i) (hc i)
  choose N hNs hNi hNc _hNcs using hex
  let B : ∀ i, Operator (V i) H := fun i => if i ∈ J then N i else A i
  have htail (i : ℕ) (hi : i ∉ J) : B i = A i := by simp only [B, ite_eq_right hi]
  refine ⟨B, ?_, ?_, finiteHead_propagation J A B r hp htail, ?_, ?_, htail⟩
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact hNs i
    · exact hs i
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact (@involution_norm_le_one (componentHilbert (V := V) (H := H) i) (N i) (hNs i) (hNi i)).trans (le_max_right _ _)
    · exact (hA i).trans (le_max_left _ _)
  · intro i
    dsimp only [B]
    split_ifs with hi
    · exact hNc i
    · rw [sub_self]
      change IsCompactOperator (0 : Module (V i) H → Module (V i) H)
      exact isCompactOperator_zero
  · intro i hi
    dsimp only [B]
    rw [ite_eq_left hi]
    exact hNi i


structure FiniteHeadReplacement (J : Finset ℕ) (A : ∀ i, Operator (V i) H) (C r : ℝ) where
  operator : ∀ i, Operator (V i) H
  selfAdjoint : ∀ i, IsSelfAdjoint (operator i)
  norm_le : ∀ i, ‖operator i‖ ≤ max C 1
  propagation : ∀ i, PropagationLE (max r (finiteHeadRadius (V := V) J)) (operator i)
  compact_diff : ∀ i, IsCompactOperator (operator i - A i)
  involutive : ∀ i, i ∈ J → operator i * operator i = 1
  tail : ∀ i, i ∉ J → operator i = A i

def finiteHeadReplacement (J : Finset ℕ) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hA : ∀ i, ‖A i‖ ≤ C) (r : ℝ)
    (hp : ∀ i, PropagationLE r (A i)) (hs : ∀ i, IsSelfAdjoint (A i))
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) :
    FiniteHeadReplacement J A C r :=
  let h := exists_finiteHead_involution J A C hA r hp hs hc
  { operator := h.choose
    selfAdjoint := h.choose_spec.1
    norm_le := h.choose_spec.2.1
    propagation := h.choose_spec.2.2.1
    compact_diff := h.choose_spec.2.2.2.1
    involutive := h.choose_spec.2.2.2.2.1
    tail := h.choose_spec.2.2.2.2.2 }

omit [SecondCountableTopology H] in
theorem FiniteHeadReplacement.square_compact {J : Finset ℕ} {A : ∀ i, Operator (V i) H} {C r : ℝ}
    (d : FiniteHeadReplacement J A C r)
    (hc : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H))) (i : ℕ) :
    IsCompactOperator (d.operator i * d.operator i - (1 : Operator (V i) H)) := by
  by_cases hi : i ∈ J
  · rw [d.involutive i hi, sub_self]
    change IsCompactOperator (0 : Module (V i) H → Module (V i) H)
    exact isCompactOperator_zero
  · rw [d.tail i hi]
    exact hc i

end CoarseAssembly.DiscreteRoe

end

end OAI
