import OAI.RingTheory.DirectFiniteness.BoundaryCycles

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {A : Type u_3} [Fintype α] [Fintype β] [AddCommGroup A]

@[simp] lemma sumCongr_sameCycle_inl (p : Perm α) (q : Perm β) (x y : α) :
    SameCycle (Equiv.sumCongr p q) (.inl x) (.inl y) ↔ p.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inl _ _ _ _

@[simp] lemma sumCongr_sameCycle_inr (p : Perm α) (q : Perm β) (x y : β) :
    SameCycle (Equiv.sumCongr p q) (.inr x) (.inr y) ↔ q.SameCycle x y := by
  change (SameCycle.setoid (Equiv.sumCongr p q)).r _ _ ↔ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_inr _ _ _ _

@[simp] lemma sumCongr_not_sameCycle (p : Perm α) (q : Perm β) (x : α) (y : β) :
    ¬ SameCycle (Equiv.sumCongr p q) (.inl x) (.inr y) := by
  change ¬ (SameCycle.setoid (Equiv.sumCongr p q)).r _ _
  rw [sumCongr_cycles_setoid]
  exact sumSetoid_cross _ _ _ _

lemma sum_cycle_sum_left (p : Perm α) (q : Perm β) (x : α) (f : α ⊕ β → A) :
    ∑ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inl x)), f y =
      ∑ y ∈ cycleSet p (cycleClass p x), f (.inl y) := by
  symm
  refine Finset.sum_bij (fun value _ => Sum.inl value) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro value member
    apply (mem_cycleSet _ _ _).mpr
    apply (cycleClass_eq _ _ _).mpr
    apply (sumCongr_sameCycle_inl p q value x).mpr
    exact (cycleClass_eq p value x).mp ((mem_cycleSet p _ value).mp member)
  · intro left _ right _ equality
    exact Sum.inl.inj equality
  · intro value member
    have related := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp member)
    cases value with
    | inl value =>
      exact ⟨value, (mem_cycleSet p _ value).mpr
        ((cycleClass_eq p value x).mpr
          ((sumCongr_sameCycle_inl p q value x).mp related)), rfl⟩
    | inr value =>
      exact False.elim (sumCongr_not_sameCycle p q x value related.symm)

lemma sum_cycle_sum_right (p : Perm α) (q : Perm β) (x : β) (f : α ⊕ β → A) :
    ∑ y ∈ cycleSet (Equiv.sumCongr p q) (cycleClass _ (.inr x)), f y =
      ∑ y ∈ cycleSet q (cycleClass q x), f (.inr y) := by
  symm
  refine Finset.sum_bij (fun value _ => Sum.inr value) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro value member
    apply (mem_cycleSet _ _ _).mpr
    apply (cycleClass_eq _ _ _).mpr
    apply (sumCongr_sameCycle_inr p q value x).mpr
    exact (cycleClass_eq q value x).mp ((mem_cycleSet q _ value).mp member)
  · intro left _ right _ equality
    exact Sum.inr.inj equality
  · intro value member
    have related := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp member)
    cases value with
    | inl value =>
      exact False.elim (sumCongr_not_sameCycle p q value x related)
    | inr value =>
      exact ⟨value, (mem_cycleSet q _ value).mpr
        ((cycleClass_eq q value x).mpr
          ((sumCongr_sameCycle_inr p q value x).mp related)), rfl⟩

def cycleInl (p : Perm α) (q : Perm β) : Cycles p → Cycles (Equiv.sumCongr p q) :=
  Quotient.map Sum.inl (fun _ _ h => (sumCongr_sameCycle_inl p q _ _).mpr h)

@[simp] lemma cycleInl_class (p : Perm α) (q : Perm β) (x : α) :
    cycleInl p q (cycleClass p x) = cycleClass _ (.inl x) := rfl

lemma cycleInl_injective (p : Perm α) (q : Perm β) :
    Function.Injective (cycleInl p q) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      change cycleClass (Equiv.sumCongr p q) (.inl x) = cycleClass _ (.inl y) →
        cycleClass p x = cycleClass p y
      simp only [cycleClass_eq, sumCongr_sameCycle_inl, imp_self]

lemma cycleInl_ne_inr (p : Perm α) (q : Perm β) (c : Cycles p) (y : β) :
    cycleInl p q c ≠ cycleClass _ (.inr y) := by
  induction c using Quotient.inductionOn with
  | h x =>
    change cycleClass (Equiv.sumCongr p q) (.inl x) ≠ cycleClass _ (.inr y)
    simp only [ne_eq, cycleClass_eq, sumCongr_not_sameCycle, not_false_eq_true]

end KaplanskyCounterexample.Planar

end

end OAI
