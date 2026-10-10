import OAI.SetTheory.PartitionPrinciple.Geometry.RationalHeightDescent

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Chronological

open Attachment

universe u

variable {O I Stage : Type u} [LinearOrder Stage] {P : MeetOrder O}
    (b : Templates.{u,u,u} P I)

theorem attachment_bridge (birth : O ⊕ b.Fresh → Stage) (s : Stage)
    (old : ∀ a, birth (.inl a) < s) (x y : b.Fresh) (different : x.1 ≠ y.1) :
    OldBridge (P := b.extension) birth s (.inr x) (.inr y) := by
  classical
  by_cases xy : b.extension.le (.inr x) (.inr y)
  · exact Or.inr (Or.inl ⟨.inl (b.shadow y), old _,
      (b.cross_le_iff x y different).mp xy, P.refl _⟩)
  · by_cases yx : b.extension.le (.inr y) (.inr x)
    · exact Or.inr (Or.inr ⟨.inl (b.shadow x), old _,
        (b.cross_le_iff y x different.symm).mp yx, P.refl _⟩)
    · apply Or.inl
      rw [b.cross_meet_eq x y different xy yx]
      exact old _

theorem attachment_essential_component (birth : O ⊕ b.Fresh → Stage) (s : Stage)
    (old : ∀ a, birth (.inl a) < s) (fresh : ∀ x : b.Fresh, birth (.inr x) = s)
    (F : MeetFilter b.extension) (x y : b.Fresh)
    (hx : Essential birth F (.inr x)) (hy : Essential birth F (.inr y)) : x.1 = y.1 := by
  by_contra different
  exact essentials_no_bridge birth F s (.inr x) (.inr y) hx hy (fresh x) (fresh y)
    (attachment_bridge b birth s old x y different)

theorem attachment_old_meet (birth : O ⊕ b.Fresh → Stage) (s : Stage)
    (old : ∀ a, birth (.inl a) < s) (fresh : ∀ x : b.Fresh, birth (.inr x) = s)
    (previous : OldMeet (P := P) (fun a => birth (.inl a))) :
    OldMeet (P := b.extension) birth := by
  intro x y earlier notLower
  cases x with
  | inl a =>
    cases y with
    | inl c =>
      have eq := (b.oldEmbedding.map_meet a c).symm
      change b.extension.meet (.inl a) (.inl c) = .inl (P.meet a c) at eq
      rw [eq]
      exact previous a c earlier notLower
    | inr y =>
      rw [fresh] at earlier
      exact False.elim (lt_asymm earlier (old a))
  | inr x =>
    cases y with
    | inl a =>
      rw [b.shadow_meet_eq x a notLower, fresh]
      exact old _
    | inr y =>
      rw [fresh, fresh] at earlier
      exact False.elim (lt_irrefl _ earlier)

def birthFresh (birth : O ⊕ b.Fresh → Stage) (s : Stage)
    (old : ∀ a, birth (.inl a) < s) (x : {x // birth x = s}) : b.Fresh := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl a =>
    have impossible := old a
    rw [hx] at impossible
    exact False.elim (lt_irrefl _ impossible)
  | inr x => exact x

theorem birthFresh_eq (birth : O ⊕ b.Fresh → Stage) (s : Stage)
    (old : ∀ a, birth (.inl a) < s) (x : {x // birth x = s}) :
    Sum.inr (birthFresh b birth s old x) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl a =>
    have impossible := old a
    rw [hx] at impossible
    exact False.elim (lt_irrefl _ impossible)
  | inr x => rfl

noncomputable def attachmentLayer (Space : Stage → Type u) (order : ∀ s, MeetOrder (Space s))
    (birth : O ⊕ b.Fresh → Stage) (s : Stage) (old : ∀ a, birth (.inl a) < s)
    (index : I → Stage) (earlier : ∀ i, index i < s)
    (template : ∀ i, MeetIso (order (index i)) (b.order i)) :
    GrowthLayer Space order b.extension birth s := by
  apply GrowthLayer.separated I index earlier
    (fun i => compose (template i).toMeetEmbedding (b.templateEmbedding i))
    (fun x => (birthFresh b birth s old x).1)
  · intro x
    let z := birthFresh b birth s old x
    refine ⟨(template z.1).inverse z.2.val, ?_⟩
    change b.represent z.1 ((template z.1).toFun ((template z.1).inverse z.2.val)) = x.val
    rw [(template z.1).right_inverse, b.represent_new z.1 z.2.val z.2.property]
    exact birthFresh_eq b birth s old x
  · intro x y different
    have bridge := attachment_bridge b birth s old
      (birthFresh b birth s old x) (birthFresh b birth s old y) different
    rw [birthFresh_eq, birthFresh_eq] at bridge
    exact bridge

def finiteLayer {A : Type u} {P : MeetOrder A} (Space : Stage → Type u)
    (order : ∀ s, MeetOrder (Space s)) (birth : A → Stage) (s : Stage)
    (finite : Set.Finite {x | birth x = s}) : GrowthLayer Space order P birth s :=
  .countablePoints finite.countable

end PartitionPilot.Compression.RecursiveMaps.Chronological

end

end OAI
