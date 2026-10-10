import OAI.Topology.CoarseAssembly.CompactBlockSum
import OAI.Topology.CoarseAssembly.ProjectionBlocks
import OAI.Topology.CoarseAssembly.AnalyticKHomology
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI

/-! # Finite active sums of analytic cycles

Countably many summands are allowed as an ambient Hilbert space; all but
finitely many cycles are degenerate. The finite active length may later
vary with the component of the coarse disjoint union.
-/

noncomputable section

namespace CoarseAssembly.Analytic

theorem diagonal_compact_of_zero_tail (H : ℕ → HilbertSpace) (K : ∀ j, End (H j))
    (T : End (countableHilbertSpace H)) (N : ℕ)
    (hT : ∀ x j, (T x) j = K j (x j))
    (hK : ∀ j, IsCompactOperator (K j)) (hzero : ∀ j, N ≤ j → K j = 0) :
    IsCompactOperator T := by
  let C := ∑ j ∈ Finset.range N, ‖K j‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => norm_nonneg (K j))
  have hb : ∀ j, ‖K j‖ ≤ C := by
    intro j
    by_cases hj : j < N
    · exact Finset.single_le_sum (fun k _ => norm_nonneg (K k)) (Finset.mem_range.mpr hj)
    · rw [hzero j (Nat.le_of_not_gt hj), norm_zero]
      exact hC
  have he : T = truncatedBlockSum H K N C hC hb := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    rw [hT, truncatedBlockSum_apply]
    by_cases hj : j < N
    · simp only [hj, ite_true]
    · simp only [hj, ite_false, hzero j (Nat.le_of_not_gt hj), zero_apply]
  rw [he]
  exact truncatedBlockSum_compact H K C hC hb hK N

variable {A : Type} [CStarAlgebra A]

abbrev familyHilbert (c : ℕ → OddCycle A) (j : ℕ) : HilbertSpace := (c j).space

def familyRepresentation (c : ℕ → OddCycle A) :
    A →⋆ₙₐ[ℂ] End (countableHilbertSpace (familyHilbert c)) where
  toFun a := blockOperator (fun j => (c j).representation a) ‖a‖ (norm_nonneg a)
    (fun j => NonUnitalStarAlgHom.norm_apply_le _ _)
  map_zero' := by
    ext x j
    change (c j).representation 0 (x j) = 0
    rw [map_zero]
    rfl
  map_add' a b := by
    ext x j
    change (c j).representation (a + b) (x j) = _
    rw [map_add]
    rfl
  map_mul' a b := by
    ext x j
    change (c j).representation (a * b) (x j) = _
    rw [map_mul]
    rfl
  map_smul' z a := by
    ext x j
    change (c j).representation (z • a) (x j) = _
    rw [map_smul]
    rfl
  map_star' a := by
    change blockOperator (fun j => (c j).representation (star a)) ‖star a‖ (norm_nonneg _)
        (fun j => NonUnitalStarAlgHom.norm_apply_le _ _) =
      (blockOperator (fun j => (c j).representation a) ‖a‖ (norm_nonneg _)
        (fun j => NonUnitalStarAlgHom.norm_apply_le _ _)).adjoint
    rw [blockOperator_adjoint]
    ext x j
    change (c j).representation (star a) (x j) = ((c j).representation a).adjoint (x j)
    rw [map_star]
    rfl

@[simp] theorem familyRepresentation_apply (c : ℕ → OddCycle A) (a : A)
    (x : countableHilbertSpace (familyHilbert c)) (j : ℕ) :
    familyRepresentation c a x j = (c j).representation a (x j) := rfl

def finiteActiveCycle (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate) : OddCycle A where
  space := countableHilbertSpace (familyHilbert c)
  representation := familyRepresentation c
  operator := blockOperator (fun j => (c j).operator) C hC hnorm
  commutator_compact a := by
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => (c j).operator * (c j).representation a - (c j).representation a * (c j).operator)
      _ N
    · intro x j
      rfl
    · exact fun j => (c j).commutator_compact a
    · exact fun j hj => (htail j hj).1 a
  square_compact a := by
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => ((c j).operator * (c j).operator - 1) * (c j).representation a) _ N
    · intro x j
      rfl
    · exact fun j => (c j).square_compact a
    · exact fun j hj => (htail j hj).2.1 a
  adjoint_compact a := by
    change IsCompactOperator
      (((blockOperator (fun j => (c j).operator) C hC hnorm).adjoint -
        blockOperator (fun j => (c j).operator) C hC hnorm) * familyRepresentation c a)
    rw [blockOperator_adjoint]
    apply diagonal_compact_of_zero_tail (familyHilbert c)
      (fun j => (star (c j).operator - (c j).operator) * (c j).representation a) _ N
    · intro x j
      rfl
    · exact fun j => (c j).adjoint_compact a
    · exact fun j hj => (htail j hj).2.2 a

theorem finiteActiveCycle_unital (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate)
    (hu : ∀ j, (c j).representation 1 = 1) :
    (finiteActiveCycle c C hC hnorm N htail).representation 1 = 1 := by
  change familyRepresentation c 1 = (1 : End (countableHilbertSpace (familyHilbert c)))
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  change (c j).representation 1 (x j) = x j
  rw [hu]
  rfl

theorem finiteActiveCycle_selfAdjoint (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate)
    (hs : ∀ j, IsSelfAdjoint (c j).operator) :
    IsSelfAdjoint (finiteActiveCycle c C hC hnorm N htail).operator := by
  change IsSelfAdjoint (blockOperator (fun j => (c j).operator) C hC hnorm)
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr (fun j => (hs j).isSymmetric (x j) (y j))

theorem finiteActiveCycle_norm (c : ℕ → OddCycle A) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ j, ‖(c j).operator‖ ≤ C) (N : ℕ)
    (htail : ∀ j, N ≤ j → (c j).Degenerate) :
    ‖(finiteActiveCycle c C hC hnorm N htail).operator‖ ≤ C :=
  blockOperator_norm_le _ _ _ _

end CoarseAssembly.Analytic

end

end OAI
