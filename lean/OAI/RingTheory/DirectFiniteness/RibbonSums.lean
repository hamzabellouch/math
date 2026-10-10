import OAI.RingTheory.DirectFiniteness.RibbonSplitting

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2}

def sumSetoid (s : Setoid α) (t : Setoid β) : Setoid (α ⊕ β) :=
  Setoid.ker (Sum.map (Quotient.mk s) (Quotient.mk t))

@[simp] lemma sumSetoid_inl (s : Setoid α) (t : Setoid β) (x y : α) :
    (sumSetoid s t).r (.inl x) (.inl y) ↔ s.r x y := by
  change (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inl (Quotient.mk s y) ↔ _
  simp only [Sum.inl.injEq, Quotient.eq]

@[simp] lemma sumSetoid_inr (s : Setoid α) (t : Setoid β) (x y : β) :
    (sumSetoid s t).r (.inr x) (.inr y) ↔ t.r x y := by
  change (Sum.inr (Quotient.mk t x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y) ↔ _
  simp only [Sum.inr.injEq, Quotient.eq]

@[simp] lemma sumSetoid_cross (s : Setoid α) (t : Setoid β) (x : α) (y : β) :
    ¬ (sumSetoid s t).r (.inl x) (.inr y) := by
  change ¬ (Sum.inl (Quotient.mk s x) : Quotient s ⊕ Quotient t) = .inr (Quotient.mk t y)
  simp

def sumSetoidEquiv (s : Setoid α) (t : Setoid β) :
    Quotient (sumSetoid s t) ≃ Quotient s ⊕ Quotient t :=
  Setoid.quotientKerEquivOfSurjective (Sum.map (Quotient.mk s) (Quotient.mk t)) (by
    rintro (x | y)
    · induction x using Quotient.inductionOn with
      | h x => exact ⟨.inl x, rfl⟩
    · induction y using Quotient.inductionOn with
      | h y => exact ⟨.inr y, rfl⟩)

lemma sumSetoid_card [Fintype α] [Fintype β] (s : Setoid α) (t : Setoid β) :
    Nat.card (Quotient (sumSetoid s t)) = Nat.card (Quotient s) + Nat.card (Quotient t) := by
  rw [Nat.card_congr (sumSetoidEquiv s t), Nat.card_sum]

lemma sumSetoid_le {s : Setoid α} {t : Setoid β} {r : Setoid (α ⊕ β)}
    (hl : ∀ x y, s.r x y → r.r (.inl x) (.inl y))
    (hr : ∀ x y, t.r x y → r.r (.inr x) (.inr y)) : sumSetoid s t ≤ r := by
  rintro (x | x) (y | y) h
  · exact hl x y ((sumSetoid_inl _ _ _ _).mp h)
  · exact False.elim (sumSetoid_cross _ _ _ _ h)
  · exact False.elim (sumSetoid_cross _ _ _ _ ((sumSetoid s t).iseqv.symm h))
  · exact hr x y ((sumSetoid_inr _ _ _ _).mp h)

variable [Fintype α] [Fintype β]

lemma sumCongr_cycles_setoid (p : Perm α) (q : Perm β) :
    SameCycle.setoid (Equiv.sumCongr p q) = sumSetoid (SameCycle.setoid p) (SameCycle.setoid q) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Equiv.sumCongr p q) _ h
    rintro (z | z) <;> simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      sumSetoid_inl, sumSetoid_inr]
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
  · apply sumSetoid_le
    · intro x y h
      exact sameCycle_map p (Equiv.sumCongr p q) Sum.inl
        (fun z => SameCycle.apply_right SameCycle.rfl) h
    · intro x y h
      exact sameCycle_map q (Equiv.sumCongr p q) Sum.inr
        (fun z => SameCycle.apply_right SameCycle.rfl) h

lemma sumCongr_cycles_card (p : Perm α) (q : Perm β) :
    Nat.card (Cycles (Equiv.sumCongr p q)) = Nat.card (Cycles p) + Nat.card (Cycles q) := by
  rw [Cycles, sumCongr_cycles_setoid]
  exact sumSetoid_card _ _

def Ribbon.sum (R : Ribbon α) (S : Ribbon β) : Ribbon (α ⊕ β) :=
  ⟨Equiv.sumCongr R.black S.black, Equiv.sumCongr R.white S.white⟩

omit [Fintype α] [Fintype β] in
lemma Ribbon.sum_face (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).face = Equiv.sumCongr R.face S.face := by
  ext x
  cases x <;> rfl

lemma Ribbon.sum_components (R : Ribbon α) (S : Ribbon β) :
    (R.sum S).components = sumSetoid R.components S.components := by
  apply le_antisymm
  · apply (R.sum S).components_le_of_steps
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.black_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.black_step x)
    · rintro (x | x)
      · exact (sumSetoid_inl _ _ _ _).mpr (R.white_step x)
      · exact (sumSetoid_inr _ _ _ _).mpr (S.white_step x)
  · apply sumSetoid_le
    · have h := R.components_le_of_steps ((R.sum S).components.comap Sum.inl)
        (fun x => (R.sum S).black_step (.inl x))
        (fun x => (R.sum S).white_step (.inl x))
      exact fun x y hxy => h hxy
    · have h := S.components_le_of_steps ((R.sum S).components.comap Sum.inr)
        (fun x => (R.sum S).black_step (.inr x))
        (fun x => (R.sum S).white_step (.inr x))
      exact fun x y hxy => h hxy

lemma Ribbon.genusZero_sum (R : Ribbon α) (S : Ribbon β)
    (hR : R.GenusZero) (hS : S.GenusZero) : (R.sum S).GenusZero := by
  unfold Ribbon.GenusZero at *
  rw [R.sum_face, R.sum_components, sumSetoid_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr R.black S.black)) +
    Nat.card (Cycles (Equiv.sumCongr R.white S.white)) + _ = _
  rw [sumCongr_cycles_card, sumCongr_cycles_card, sumCongr_cycles_card]
  omega

omit [Fintype α] [Fintype β] in
lemma formPerm_append_nonempty [DecidableEq α] (a b : α) (l m : List α)
    (hb : b ∉ a :: l) :
    ((a :: l) ++ (b :: m)).formPerm = swap a b * (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    have hba : b ≠ a := fun h => hb (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have hc : b ∉ c :: l := fun h => hb (List.mem_cons_of_mem _ h)
    have hs : swap a c * swap c b = swap a b * swap a c := by
      rw [mul_swap_eq_swap_mul]
      simp [swap_apply_of_ne_of_ne hba hbc]
    simp only [List.cons_append, List.formPerm_cons_cons]
    rw [show c :: (l ++ b :: m) = (c :: l) ++ (b :: m) from rfl, ih c hc]
    simp only [← mul_assoc, hs]

end KaplanskyCounterexample.Planar

end

end OAI
