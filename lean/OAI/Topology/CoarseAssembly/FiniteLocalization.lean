import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CycleCompactPerturbation
import Mathlib.Algebra.Star.BigOperators

namespace OAI

/-! # Finite partition localization of Fredholm cycles

This is the operator step used on each compact Rips component. A represented
square partition of unity localizes the operator without changing its cycle
class. The geometric partition and its propagation control are constructed
separately.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {ι : Type*} [Fintype ι]

theorem localizedOperator_sub_eq (c : OddCycle A) (a : ι → A)
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    localizedOperator c a - c.operator =
      ∑ i, c.representation (a i) *
        (c.operator * c.representation (a i) - c.representation (a i) * c.operator) := by
  calc
    localizedOperator c a - c.operator = localizedOperator c a -
        (∑ i, c.representation (a i) * c.representation (a i)) * c.operator := by
      rw [hpart, one_mul]
    _ = ∑ i, (c.representation (a i) * c.operator * c.representation (a i) -
        (c.representation (a i) * c.representation (a i)) * c.operator) := by
      rw [localizedOperator, Finset.sum_mul, ← Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring

theorem localizedOperator_sub_compact (c : OddCycle A) (a : ι → A)
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    IsCompactOperator (localizedOperator c a - c.operator) := by
  rw [localizedOperator_sub_eq c a hpart]
  exact (compactOperator (RingHom.id ℂ) c.space c.space).sum_mem
    (fun i _ => compact_mul_left (c.commutator_compact (a i)) _)

theorem localizedOperator_selfAdjoint (c : OddCycle A) (a : ι → A)
    (hF : IsSelfAdjoint c.operator) (ha : ∀ i, IsSelfAdjoint (a i)) :
    IsSelfAdjoint (localizedOperator c a) :=
  isSelfAdjoint_sum _ (fun i _ => hF.conjugate_self ((ha i).map c.representation))

@[simp] theorem localizedCycle_operator (c : OddCycle A) (a : ι → A)
    (hF : IsSelfAdjoint c.operator) (ha : ∀ i, IsSelfAdjoint (a i))
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    (localizedCycle c a hF ha hpart).operator = localizedOperator c a := by
  change c.operator + (localizedOperator c a - c.operator) = localizedOperator c a
  abel

theorem localizedCycle_class (c : OddCycle A) (a : ι → A)
    (hF : IsSelfAdjoint c.operator) (ha : ∀ i, IsSelfAdjoint (a i))
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    cycleClass A (localizedCycle c a hF ha hpart) = cycleClass A c :=
  compactPerturb_class c (localizedOperator c a - c.operator)
    (localizedOperator_sub_compact c a hpart) (by
      rw [((localizedOperator_selfAdjoint c a hF ha).sub hF).star_eq]
      exact localizedOperator_sub_compact c a hpart)

end CoarseAssembly.Analytic

end

end OAI
