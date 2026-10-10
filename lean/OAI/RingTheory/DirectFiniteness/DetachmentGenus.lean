import OAI.RingTheory.DirectFiniteness.RibbonDetachment

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

omit [Fintype α] in
lemma Ribbon.face_step (R : Ribbon α) (x : α) : R.components.r x (R.face x) :=
  R.components.iseqv.trans (R.black_step x) (R.white_step (R.black x))

lemma Ribbon.sameCycle_face_components (R : Ribbon α) {x y : α} (h : R.face.SameCycle x y) :
    R.components.r x y := setoid_sameCycle_of_step R.components R.face R.face_step h

lemma Ribbon.detach_components_card (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) +
      if (R.detach a).components.r (R.black a) (R.white a) then 1 else 2 := by
  let s := (R.detach a).components
  let t := joinPair s a (R.black a)
  have hb' : ¬ s.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have hw' : ¬ s.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have ht : Nat.card (Quotient t) + 1 = Nat.card (Quotient s) := joinPair_card s _ _ hb'
  have heq : R.components = joinPair t a (R.white a) := R.components_detach a
  by_cases h : s.r (R.black a) (R.white a)
  · have h' : t.r a (R.white a) := (joinPair_left_iff s _ _ _).mpr (Or.inr h)
    rw [joinPair_eq_of_related _ h'] at heq
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_true, heq]
    omega
  · have h' : ¬ t.r a (R.white a) := by
      rw [joinPair_left_iff]
      exact not_or.mpr ⟨hw', h⟩
    have ht' := joinPair_card t a (R.white a) h'
    rw [← heq] at ht'
    change Nat.card (Quotient s) = Nat.card (Quotient R.components) + if s.r (R.black a) (R.white a) then 1 else 2
    simp only [h, ite_false]
    omega

lemma Ribbon.detach_components_card_black_fixed (R : Ribbon α) (a : α)
    (hb : R.black a = a) (hw : R.white a ≠ a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.white a) := fun h => hw (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hb, joinPair_eq_of_related _ ((R.detach a).components.iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.white a) hn
  rw [← heq] at hc
  omega

lemma Ribbon.detach_components_card_white_fixed (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a = a) :
    Nat.card (Quotient (R.detach a).components) = Nat.card (Quotient R.components) + 1 := by
  have hn : ¬ (R.detach a).components.r a (R.black a) := fun h => hb (R.detach_isolated a h)
  have heq := R.components_detach a
  rw [hw, joinPair_eq_of_related _ ((joinPair (R.detach a).components a (R.black a)).iseqv.refl a)] at heq
  have hc := joinPair_card (R.detach a).components a (R.black a) hn
  rw [← heq] at hc
  omega

omit [Fintype α] in
lemma Ribbon.detach_face_black_fixed (R : Ribbon α) (a : α) (hb : R.black a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face]
  have hf : R.face a = R.white a := by simp [Ribbon.face, hb]
  simp [hf, unplug]
  rfl

omit [Fintype α] in
lemma Ribbon.detach_face_white_fixed (R : Ribbon α) (a : α) (hw : R.white a = a) :
    (R.detach a).face = unplug R.face a := by
  rw [R.detach_face, hw]
  simp [unplug]
  rfl

lemma Ribbon.detach_face_card_separating (R : Ribbon α) (a : α)
    (hb : R.black a ≠ a) (hw : R.white a ≠ a)
    (hsep : ¬ (R.detach a).components.r (R.black a) (R.white a)) :
    Nat.card (Cycles (R.detach a).face) = Nat.card (Cycles R.face) + 2 := by
  have hf : R.face a ≠ a := by
    intro hf
    have hs : (R.detach a).white (R.black a) = R.white a := by
      change swap a (R.white a) (R.face a) = R.white a
      simp [hf]
    exact hsep (hs ▸ (R.detach a).white_step (R.black a))
  have hs : (R.detach a).white (R.black a) = R.face a := by
    change swap a (R.white a) (R.face a) = R.face a
    exact swap_apply_of_ne_of_ne hf (R.white.injective.ne hb)
  have hnot : ¬ (R.detach a).face.SameCycle (R.white a) (R.face a) := by
    intro h
    have hc := (R.detach a).sameCycle_face_components h
    have hs' := (R.detach a).white_step (R.black a)
    rw [hs] at hs'
    exact hsep ((R.detach a).components.iseqv.trans hs'
      ((R.detach a).components.iseqv.symm hc))
  have hcard := swap_mul_cycles_card (R.detach a).face (R.white a) (R.face a) hnot
  have heq : swap (R.white a) (R.face a) * (R.detach a).face = unplug R.face a := by
    rw [R.detach_face_unplug a hw hf]
    simp [← mul_assoc]
  rw [heq, unplug_cycles_card R.face a hf] at hcard
  omega

/-- Edge deletion preserves genus zero, including when deletion separates a
component or removes a vertex of degree one. The detached edge is represented
as an isolated one-edge component until restriction discards it. -/
theorem Ribbon.genusZero_detach (R : Ribbon α) (hR : R.GenusZero) (a : α) :
    (R.detach a).GenusZero := by
  by_cases hb : R.black a = a
  · have hblack : (R.detach a).black = R.black := by
      simp [Ribbon.detach, unplug, hb]
      rfl
    by_cases hw : R.white a = a
    · have heq : R.detach a = R := by
        cases R
        simp_all [Ribbon.detach, unplug]
      rwa [heq]
    · have hwc := unplug_cycles_card R.white a hw
      have hcc := R.detach_components_card_black_fixed a hb hw
      have hf : R.face a ≠ a := by simpa [Ribbon.face, hb] using hw
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_black_fixed a hb] at hfc
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hblack, hwc, hfc, hcc]
      simp only [Nat.mul_add, Nat.mul_one]
      repeat rw [← Nat.add_assoc]
      rw [Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
        1 (Nat.card (Cycles R.face))]
      exact congrArg (· + 2) hR
  · have hbc := unplug_cycles_card R.black a hb
    change Nat.card (Cycles (R.detach a).black) = _ at hbc
    by_cases hw : R.white a = a
    · have hwhite : (R.detach a).white = R.white := by
        simp [Ribbon.detach, unplug, hw]
        rfl
      have hcc := R.detach_components_card_white_fixed a hb hw
      have hf : R.face a ≠ a := by
        intro hf
        apply hb
        apply R.white.injective
        simpa [Ribbon.face, hw] using hf
      have hfc := unplug_cycles_card R.face a hf
      rw [← R.detach_face_white_fixed a hw] at hfc
      unfold Ribbon.GenusZero at hR ⊢
      rw [hwhite, hbc, hfc, hcc]
      simp only [Nat.mul_add, Nat.mul_one]
      repeat rw [← Nat.add_assoc]
      rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
        Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
          1 (Nat.card (Cycles R.face))]
      exact congrArg (· + 2) hR
    · have hwc := unplug_cycles_card R.white a hw
      change Nat.card (Cycles (R.detach a).white) = _ at hwc
      have hcc := R.detach_components_card a hb hw
      by_cases hs : (R.detach a).components.r (R.black a) (R.white a)
      · rw [ite_eq_left hs] at hcc
        have hfc := R.detach_face_card_le a hw
        have hbound := (R.detach a).euler_le
        unfold Ribbon.GenusZero at hR ⊢
        apply le_antisymm hbound
        rw [hbc, hwc, hcc]
        simp only [Nat.mul_add, Nat.mul_one]
        repeat rw [← Nat.add_assoc]
        rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + 1)
            1 (Nat.card (Cycles (R.detach a).face)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
            1 (Nat.card (Cycles (R.detach a).face)), ← hR]
        exact Nat.add_le_add_right (Nat.add_le_add_left hfc _) 2
      · rw [ite_eq_right hs] at hcc
        have hfc := R.detach_face_card_separating a hb hw hs
        unfold Ribbon.GenusZero at hR ⊢
        rw [hbc, hwc, hfc, hcc]
        simp only [Nat.mul_add]
        repeat rw [← Nat.add_assoc]
        rw [Nat.add_right_comm (Nat.card (Cycles R.black)) 1 (Nat.card (Cycles R.white)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + 1)
            1 (Nat.card (Cycles R.face)),
          Nat.add_right_comm (Nat.card (Cycles R.black) + Nat.card (Cycles R.white))
            1 (Nat.card (Cycles R.face))]
        exact congrArg (· + 4) hR

end KaplanskyCounterexample.Planar

end

end OAI
