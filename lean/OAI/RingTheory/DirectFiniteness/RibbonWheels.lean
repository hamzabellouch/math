import OAI.RingTheory.DirectFiniteness.RibbonSums

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

/-- A planar two-vertex wheel: opposite rotations and matching white bivalent
vertices. Empty and singleton rotations are included. -/
def Ribbon.wheel (p : Perm α) : Ribbon (α ⊕ α) :=
  ⟨Equiv.sumCongr p p⁻¹, Equiv.sumComm α α⟩

def sumIndex : α ⊕ α → α := Sum.elim id id

def wheelFaceIndex (p : Perm α) : α ⊕ α → α := Sum.elim id (fun x => p⁻¹ x)

omit [Fintype α] in
@[simp] lemma wheel_white_index (p : Perm α) (x : α ⊕ α) :
    sumIndex ((Ribbon.wheel p).white x) = sumIndex x := by cases x <;> rfl

omit [Fintype α] in
@[simp] lemma wheel_face_index (p : Perm α) (x : α ⊕ α) :
    wheelFaceIndex p ((Ribbon.wheel p).face x) = wheelFaceIndex p x := by
  cases x <;> simp [Ribbon.wheel, Ribbon.face, wheelFaceIndex]

lemma wheel_white_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).white = Setoid.ker sumIndex := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).white _ h
    exact fun z => (wheel_white_index p z).symm
  · rintro (x | x) (y | y) h <;> change x = y at h <;> subst y
    · exact SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.apply_right SameCycle.rfl
    · exact SameCycle.rfl

lemma wheel_face_setoid (p : Perm α) :
    SameCycle.setoid (Ribbon.wheel p).face = Setoid.ker (wheelFaceIndex p) := by
  apply le_antisymm
  · intro x y h
    apply setoid_sameCycle_of_step _ (Ribbon.wheel p).face _ h
    exact fun z => (wheel_face_index p z).symm
  · rintro (x | x) (y | y) h
    · change x = y at h
      subst y
      exact SameCycle.rfl
    · change x = p⁻¹ y at h
      subst x
      change (Ribbon.wheel p).face.SameCycle (.inl (p⁻¹ y)) (.inr y)
      convert (SameCycle.apply_right
        (SameCycle.rfl (f := (Ribbon.wheel p).face) (x := Sum.inl (p⁻¹ y)))) using 1
      simp [Ribbon.wheel, Ribbon.face]
    · change p⁻¹ x = y at h
      subst y
      exact SameCycle.apply_right SameCycle.rfl
    · change p⁻¹ x = p⁻¹ y at h
      have := p.symm.injective h
      subst y
      exact SameCycle.rfl

lemma wheel_component_index (p : Perm α) :
    (Ribbon.wheel p).components = Setoid.ker (cycleClass p ∘ sumIndex) := by
  let R := Ribbon.wheel p
  apply le_antisymm
  · apply R.components_le_of_steps
    · rintro (x | x)
      · exact (cycleClass_apply p x).symm
      · change cycleClass p x = cycleClass p (p⁻¹ x)
        exact (cycleClass_eq _ _ _).mpr SameCycle.rfl.symm_apply_right
    · intro x
      change cycleClass p (sumIndex x) = cycleClass p (sumIndex (R.white x))
      rw [wheel_white_index]
  · intro x y h
    have hx : R.components.r x (.inl (sumIndex x)) := by
      cases x with
      | inl x => exact R.components.iseqv.refl _
      | inr x => exact R.white_step (.inr x)
    have hy : R.components.r y (.inl (sumIndex y)) := by
      cases y with
      | inl y => exact R.components.iseqv.refl _
      | inr y => exact R.white_step (.inr y)
    have hxy : p.SameCycle (sumIndex x) (sumIndex y) := (cycleClass_eq _ _ _).mp h
    have hp : R.black.SameCycle (.inl (sumIndex x)) (.inl (sumIndex y)) :=
      sameCycle_map p R.black Sum.inl (fun z => SameCycle.apply_right SameCycle.rfl) hxy
    exact R.components.iseqv.trans hx (R.components.iseqv.trans
      ((show SameCycle.setoid R.black ≤ R.components from le_sup_left) hp)
      (R.components.iseqv.symm hy))

lemma wheel_white_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).white) = Fintype.card α := by
  rw [Cycles, wheel_white_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective sumIndex
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_face_card (p : Perm α) :
    Nat.card (Cycles (Ribbon.wheel p).face) = Fintype.card α := by
  rw [Cycles, wheel_face_setoid]
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective (wheelFaceIndex p)
    (fun x => ⟨.inl x, rfl⟩))).trans Nat.card_eq_fintype_card

lemma wheel_component_card (p : Perm α) :
    Nat.card (Quotient (Ribbon.wheel p).components) = Nat.card (Cycles p) := by
  rw [wheel_component_index]
  apply Nat.card_congr
  apply Setoid.quotientKerEquivOfSurjective
  intro c
  induction c using Quotient.inductionOn with
  | h x => exact ⟨.inl x, rfl⟩

lemma Ribbon.genusZero_wheel (p : Perm α) : (Ribbon.wheel p).GenusZero := by
  unfold Ribbon.GenusZero
  rw [wheel_white_card, wheel_face_card, wheel_component_card, Fintype.card_sum]
  change Nat.card (Cycles (Equiv.sumCongr p p⁻¹)) + _ + _ = _
  rw [sumCongr_cycles_card, cycles_inv_card]
  omega

end KaplanskyCounterexample.Planar

end

end OAI
