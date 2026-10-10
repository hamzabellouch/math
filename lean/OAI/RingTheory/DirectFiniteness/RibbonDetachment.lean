import OAI.RingTheory.DirectFiniteness.RibbonRestriction

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
lemma Ribbon.black_step (R : Ribbon α) (x : α) : R.components.r x (R.black x) :=
  (show SameCycle.setoid R.black ≤ R.components from le_sup_left) (show R.black.SameCycle x (R.black x) from SameCycle.apply_right SameCycle.rfl)

omit [Fintype α] in
lemma Ribbon.white_step (R : Ribbon α) (x : α) : R.components.r x (R.white x) :=
  (show SameCycle.setoid R.white ≤ R.components from le_sup_right) (show R.white.SameCycle x (R.white x) from SameCycle.apply_right SameCycle.rfl)

lemma Ribbon.components_le_of_steps (R : Ribbon α) (s : Setoid α)
    (hb : ∀ x, s.r x (R.black x)) (hw : ∀ x, s.r x (R.white x)) : R.components ≤ s := by
  exact sup_le (fun _ _ h => setoid_sameCycle_of_step s R.black hb h)
    (fun _ _ h => setoid_sameCycle_of_step s R.white hw h)

omit [Fintype α] in
lemma Ribbon.black_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.black x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.black_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.black_step x))

omit [Fintype α] in
lemma Ribbon.white_component_invariant (R : Ribbon α) (a x : α) :
    R.components.r (R.white x) a ↔ R.components.r x a := by
  constructor
  · exact R.components.iseqv.trans (R.white_step x)
  · exact R.components.iseqv.trans (R.components.iseqv.symm (R.white_step x))

/-- Retain the connected component of an edge. -/
def Ribbon.keepComponent (R : Ribbon α) (a : α) : Ribbon {x // R.components.r x a} :=
  R.restrict (fun x => R.components.r x a) (R.black_component_invariant a)
    (R.white_component_invariant a)

lemma Ribbon.keepComponent_card (R : Ribbon α) (a : α) :
    Nat.card (Quotient (R.keepComponent a).components) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ ⟨a, R.components.iseqv.refl a⟩, ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    change (R.restrict _ _ _).components.r x ⟨a, _⟩
    rw [R.restrict_components]
    exact x.prop

lemma Ribbon.spherical_keepComponent (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.keepComponent a).Spherical := by
  have h := R.planar_restrict hR (fun x => R.components.r x a)
    (R.black_component_invariant a) (R.white_component_invariant a)
  change (R.keepComponent a).GenusZero at h
  unfold Ribbon.GenusZero at h
  rw [R.keepComponent_card] at h
  exact h

omit [Fintype α] in
lemma joinPair_left_iff (s : Setoid α) (a b y : α) :
    (joinPair s a b).r a y ↔ s.r a y ∨ s.r b y := by
  change mergeClass s a b a = mergeClass s a b y ↔ _
  have ha : mergeClass s a b a = Quotient.mk s a := by simp [mergeClass]
  rw [ha]
  by_cases hy : Quotient.mk s y = Quotient.mk s b
  · simp only [mergeClass, hy, ite_true, true_iff]
    exact Or.inr (s.iseqv.symm (Quotient.exact hy))
  · simp only [mergeClass, hy, ite_false, Quotient.eq]
    exact or_iff_left (fun h => hy (Quotient.sound (s.iseqv.symm h))) |>.symm

/-- Detach an edge from both endpoint rotations. It then forms a separate
one-edge component and can be discarded by restricting to its complement. -/
def Ribbon.detach (R : Ribbon α) (a : α) : Ribbon α where
  black := unplug R.black a
  white := unplug R.white a

omit [Fintype α] in
lemma Ribbon.detach_fixed_black (R : Ribbon α) (a : α) : (R.detach a).black a = a :=
  unplug_fixed _ _
omit [Fintype α] in
lemma Ribbon.detach_fixed_white (R : Ribbon α) (a : α) : (R.detach a).white a = a :=
  unplug_fixed _ _

lemma Ribbon.detach_isolated (R : Ribbon α) (a : α) {x : α}
    (h : (R.detach a).components.r a x) : x = a := by
  have hb : ∀ x, (R.detach a).black x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).black.injective
      simpa only [R.detach_fixed_black] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_black a
  have hw : ∀ x, (R.detach a).white x = a ↔ x = a := by
    intro x
    constructor
    · intro h
      apply (R.detach a).white.injective
      simpa only [R.detach_fixed_white] using h
    · intro hx
      simpa only [hx] using R.detach_fixed_white a
  exact ((R.detach a).invariant_components (fun x => x = a) hb hw h).mp rfl

lemma Ribbon.detach_components_le (R : Ribbon α) (a : α) :
    (R.detach a).components ≤ R.components := by
  apply sup_le
  · exact fun _ _ h => (show SameCycle.setoid R.black ≤ R.components from le_sup_left)
      (unplug_sameCycle R.black a h)
  · exact fun _ _ h => (show SameCycle.setoid R.white ≤ R.components from le_sup_right)
      (unplug_sameCycle R.white a h)

lemma Ribbon.components_detach (R : Ribbon α) (a : α) :
    R.components = joinPair (joinPair (R.detach a).components a (R.black a)) a (R.white a) := by
  let s := (R.detach a).components
  let t := joinPair (joinPair s a (R.black a)) a (R.white a)
  apply le_antisymm
  · apply R.components_le_of_steps t
    · intro x
      have hstep : t.r x ((R.detach a).black x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).black_step x))
      have hab : t.r a (R.black a) := le_joinPair _ _ _ (joinPair_related _ _ _)
      have hback : swap a (R.black a) ((R.detach a).black x) = R.black x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
    · intro x
      have hstep : t.r x ((R.detach a).white x) :=
        le_joinPair _ _ _ (le_joinPair _ _ _ ((R.detach a).white_step x))
      have hab : t.r a (R.white a) := joinPair_related _ _ _
      have hback : swap a (R.white a) ((R.detach a).white x) = R.white x := by
        simp [Ribbon.detach, unplug]
      rw [← hback]
      exact t.iseqv.trans hstep (setoid_swap_related t hab _)
  · apply joinPair_le
    · exact joinPair_le _ _ _ _ (R.detach_components_le a) (R.black_step a)
    · exact R.white_step a

omit [Fintype α] in
lemma Ribbon.detach_face (R : Ribbon α) (a : α) :
    (R.detach a).face = swap a (R.white a) * swap (R.white a) (R.face a) * R.face := by
  simp only [Ribbon.detach, Ribbon.face, unplug, mul_assoc]
  rw [← mul_assoc R.white (swap a (R.black a)), mul_swap_eq_swap_mul]
  simp only [Perm.mul_apply, mul_assoc]

omit [Fintype α] in
lemma Ribbon.detach_face_of_face_fixed (R : Ribbon α) (a : α) (ha : R.face a = a) :
    (R.detach a).face = R.face := by
  rw [R.detach_face, ha, swap_comm (R.white a) a]
  simp

omit [Fintype α] in
lemma Ribbon.detach_face_unplug (R : Ribbon α) (a : α)
    (hw : R.white a ≠ a) (hf : R.face a ≠ a) :
    (R.detach a).face = swap (R.white a) (R.face a) * unplug R.face a := by
  rw [R.detach_face, swap_mul_eq_mul_swap]
  have ha : swap (R.white a) (R.face a) a = a := swap_apply_of_ne_of_ne hw.symm hf.symm
  simp only [swap_inv, ha, swap_apply_left, unplug, mul_assoc]

lemma Ribbon.detach_face_card_le (R : Ribbon α) (a : α) (hw : R.white a ≠ a) :
    Nat.card (Cycles R.face) ≤ Nat.card (Cycles (R.detach a).face) := by
  by_cases hf : R.face a = a
  · rw [R.detach_face_of_face_fixed a hf]
  · have h := swap_cycles_card_le (R.detach a).face (R.white a) (R.face a)
    rw [R.detach_face_unplug a hw hf] at h
    simp only [← mul_assoc, swap_mul_self, one_mul] at h
    have hc := unplug_cycles_card R.face a hf
    rw [R.detach_face_unplug a hw hf]
    omega

end KaplanskyCounterexample.Planar

end

end OAI
