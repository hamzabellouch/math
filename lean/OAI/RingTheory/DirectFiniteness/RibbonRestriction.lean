import OAI.RingTheory.DirectFiniteness.EulerBound

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

def restrictQuotient (s : Setoid α) (P : α → Prop) :
    Quotient (s.comap (Subtype.val : {x // P x} → α)) → Quotient s :=
  Quotient.map Subtype.val (fun _ _ h => h)

lemma restrictQuotient_injective (s : Setoid α) (P : α → Prop) :
    Function.Injective (restrictQuotient s P) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h x y =>
    intro h
    change Quotient.mk s x.val = Quotient.mk s y.val at h
    apply Quotient.sound
    change s.r x.val y.val
    exact Quotient.exact h

/-- Components of an invariant subset and of its complement partition the
components of the original finite set. -/
def quotientRestrictSumEquiv (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    (Quotient (s.comap (Subtype.val : {x // P x} → α)) ⊕
      Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) ≃ Quotient s :=
  Equiv.ofBijective (Sum.elim (restrictQuotient s P) (restrictQuotient s (fun x => ¬ P x))) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (restrictQuotient_injective s P hab)
        | inr b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (b.prop ((hP (Quotient.exact hab)).mp a.prop)).elim
      | inr a =>
        cases b with
        | inl b =>
          induction a, b using Quotient.inductionOn₂ with
          | h a b => exact (a.prop ((hP (Quotient.exact hab)).mpr b.prop)).elim
        | inr b => exact congrArg Sum.inr (restrictQuotient_injective s _ hab)
    · intro c
      induction c using Quotient.inductionOn with
      | h x =>
        by_cases hx : P x
        · exact ⟨Sum.inl (Quotient.mk _ ⟨x, hx⟩), rfl⟩
        · exact ⟨Sum.inr (Quotient.mk _ ⟨x, hx⟩), rfl⟩)

lemma quotient_restrict_card_split [Fintype α] (s : Setoid α) (P : α → Prop)
    (hP : ∀ {x y}, s.r x y → (P x ↔ P y)) :
    Nat.card (Quotient (s.comap (Subtype.val : {x // P x} → α))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x // ¬ P x} → α))) =
      Nat.card (Quotient s) := by
  simpa only [Nat.card_sum] using Nat.card_congr (quotientRestrictSumEquiv s P hP)

variable [Fintype α]

lemma perm_invariant_cycle (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    {x y : α} (hxy : p.SameCycle x y) : P x ↔ P y := by
  exact Iff.of_eq (setoid_sameCycle_of_step (Setoid.ker P) p
    (fun x => propext (hP x).symm) hxy)

omit [Fintype α] in
lemma subtype_cycles_setoid (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    SameCycle.setoid (p.subtypePerm hP) =
      (SameCycle.setoid p).comap (Subtype.val : {x // P x} → α) := by
  ext x y
  exact sameCycle_subtypePerm

lemma cycles_restrict_card_split (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Nat.card (Cycles (p.subtypePerm hP)) +
      Nat.card (Cycles (p.subtypePerm (p := fun x => ¬ P x) fun x => not_congr (hP x))) = Nat.card (Cycles p) := by
  unfold Cycles
  rw [subtype_cycles_setoid, subtype_cycles_setoid]
  exact quotient_restrict_card_split _ P (perm_invariant_cycle p P hP)

/-- Restrict a ribbon to a union of its connected components. -/
def Ribbon.restrict (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x) :
    Ribbon {x // P x} where
  black := R.black.subtypePerm hb
  white := R.white.subtypePerm hw

omit [Fintype α] in
lemma Ribbon.restrict_face (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).face = R.face.subtypePerm (fun x => (hw _).trans (hb x)) := rfl

lemma Ribbon.invariant_components (R : Ribbon α) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    {x y : α} (hxy : R.components.r x y) : P x ↔ P y := by
  have h : R.components ≤ Setoid.ker P := by
    apply sup_le
    · exact fun _ _ h => propext (perm_invariant_cycle R.black P hb h)
    · exact fun _ _ h => propext (perm_invariant_cycle R.white P hw h)
  exact Iff.of_eq (h hxy)

lemma Ribbon.restrict_components (R : Ribbon α) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).components =
      R.components.comap (Subtype.val : {x // P x} → α) := by
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid R.black ≤ R.components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mp h)
    · intro x y h
      exact (show SameCycle.setoid R.white ≤ R.components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mp h)
  · intro x y hxy
    change R.components.r x.val y.val at hxy
    have hmain : ∀ {a b : α}, R.components.r a b → ∀ (ha : P a) (hb' : P b),
        (R.restrict P hb hw).components.r ⟨a, ha⟩ ⟨b, hb'⟩ := by
      intro a b h
      rw [Ribbon.components, Setoid.sup_def] at h
      change Relation.EqvGen (fun a b => R.black.SameCycle a b ∨ R.white.SameCycle a b) a b at h
      induction h with
      | rel a b hab =>
        intro ha hb'
        rcases hab with hab | hab
        · exact (show SameCycle.setoid (R.restrict P hb hw).black ≤ (R.restrict P hb hw).components from le_sup_left) ((sameCycle_subtypePerm (h := hb)).mpr hab)
        · exact (show SameCycle.setoid (R.restrict P hb hw).white ≤ (R.restrict P hb hw).components from le_sup_right) ((sameCycle_subtypePerm (h := hw)).mpr hab)
      | refl a => exact fun _ _ => (R.restrict P hb hw).components.iseqv.refl _
      | symm a b hab ih =>
        intro ha hb'
        exact (R.restrict P hb hw).components.iseqv.symm (ih hb' ha)
      | trans a b c hab hbc ihab ihbc =>
        intro ha hc
        have hab' : R.components.r a b := by
          rw [Ribbon.components, Setoid.sup_def]
          exact hab
        have hb' : P b := (R.invariant_components P hb hw hab').mp ha
        exact (R.restrict P hb hw).components.iseqv.trans (ihab ha hb') (ihbc hb' hc)
    exact hmain hxy x.prop y.prop

/-- Euler equality componentwise, i.e., genus zero for all components. -/
def Ribbon.GenusZero (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) =
    Fintype.card α + 2 * Nat.card (Quotient R.components)

lemma Ribbon.planar_restrict (R : Ribbon α) (hR : R.GenusZero) (P : α → Prop) (hb hw) :
    (R.restrict P hb hw).GenusZero := by
  let S := R.restrict P hb hw
  let T := R.restrict (fun x => ¬ P x) (fun x => not_congr (hb x)) (fun x => not_congr (hw x))
  have hs := S.euler_le
  have ht := T.euler_le
  have hbc := cycles_restrict_card_split R.black P hb
  have hwc := cycles_restrict_card_split R.white P hw
  have hfc := cycles_restrict_card_split R.face P (fun x => (hw _).trans (hb x))
  have hcc := quotient_restrict_card_split R.components P (R.invariant_components P hb hw)
  rw [← R.restrict_components P hb hw,
    ← R.restrict_components (fun x => ¬ P x) (fun x => not_congr (hb x))
      (fun x => not_congr (hw x))] at hcc
  have hec : Fintype.card {x // P x} + Fintype.card {x // ¬ P x} = Fintype.card α := by
    have h := Fintype.card_subtype_compl P
    have hle := Fintype.card_subtype_le P
    omega
  change Nat.card (Cycles S.black) + Nat.card (Cycles T.black) = _ at hbc
  change Nat.card (Cycles S.white) + Nat.card (Cycles T.white) = _ at hwc
  change Nat.card (Cycles S.face) + Nat.card (Cycles T.face) = _ at hfc
  change Nat.card (Quotient S.components) + Nat.card (Quotient T.components) = _ at hcc
  unfold Ribbon.GenusZero at hR ⊢
  change Nat.card (Cycles S.black) + Nat.card (Cycles S.white) + Nat.card (Cycles S.face) =
    Fintype.card {x // P x} + 2 * Nat.card (Quotient S.components)
  omega

end KaplanskyCounterexample.Planar

end

end OAI
