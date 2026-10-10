import OAI.SetTheory.PartitionPrinciple.Transfinite.CountableCoding

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

structure HeightOrder (H : Type v) where
  lt : H → H → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z

namespace HeightOrder

variable {H : Type v} (R : HeightOrder H)

def Weak (x y : H) : Prop := x = y ∨ R.lt x y

theorem weak_lt {x y z : H} (h : R.Weak x y) (h' : R.lt y z) : R.lt x z := by
  rcases h with eq | h
  · cases eq
    exact h'
  · exact R.trans h h'

theorem lt_weak {x y z : H} (h : R.lt x y) (h' : R.Weak y z) : R.lt x z := by
  rcases h' with eq | h'
  · cases eq
    exact h
  · exact R.trans h h'

end HeightOrder

structure StrictHeight {A : Type u} {H : Type v} (P : MeetOrder A) (R : HeightOrder H) where
  value : A → H
  strict : ∀ x y, P.le x y → x ≠ y → R.lt (value x) (value y)

namespace StrictHeight

variable {A : Type u} {H : Type v} {P : MeetOrder A} {R : HeightOrder H}

theorem mono (h : StrictHeight P R) {x y : A} (lower : P.le x y) : R.Weak (h.value x) (h.value y) := by
  classical
  by_cases eq : x = y
  · exact Or.inl (congrArg h.value eq)
  · exact Or.inr (h.strict x y lower eq)

def precompose {B : Type w} {Q : MeetOrder B} (h : StrictHeight P R)
    (e : MeetEmbedding Q P) : StrictHeight Q R where
  value x := h.value (e.toFun x)
  strict _ _ lower different := h.strict _ _ ((e.le_iff _ _).mpr lower)
    (fun eq => different (embedding_injective e eq))

end StrictHeight

namespace AttachmentHeight

variable {O : Type u} {I : Type w} {H : Type z} {P : MeetOrder O} {R : HeightOrder H}
    (b : Templates.{u,v,w} P I) (old : StrictHeight P R)
    (component : ∀ i, StrictHeight (b.order i) R)

def value : O ⊕ b.Fresh → H
  | .inl x => old.value x
  | .inr x => (component x.1).value x.2.val

theorem strict
    (lower : ∀ x : b.Fresh, R.lt (old.value (b.base x.1)) ((component x.1).value x.2.val))
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1)))
    (x y : O ⊕ b.Fresh) (le : b.extension.le x y) (different : x ≠ y) :
    R.lt (value b old component x) (value b old component y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact old.strict x y le (fun eq => different (congrArg Sum.inl eq))
    | inr y =>
      have below : P.le x (b.base y.1) := P.trans le (b.data.shadow_le_base y)
      exact R.weak_lt (old.mono below) (lower y)
  | inr x =>
    cases y with
    | inl y => exact R.lt_weak (upper x) (old.mono (b.separator_le_upper x.1 y le))
    | inr y =>
      rcases le with inside | cross
      · rcases x with ⟨i, x, hx⟩
        rcases y with ⟨j, y, hy⟩
        rcases inside with ⟨same, inside⟩
        cases same
        apply (component i).strict x y inside
        intro eq
        cases eq
        exact different rfl
      · have middle : P.le (b.separator x.1) (b.base y.1) :=
          P.trans (b.separator_le_upper x.1 (b.shadow y) cross) (b.data.shadow_le_base y)
        exact R.trans (upper x) (R.weak_lt (old.mono middle) (lower y))

def extend
    (lower : ∀ x : b.Fresh, R.lt (old.value (b.base x.1)) ((component x.1).value x.2.val))
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1))) :
    StrictHeight b.extension R where
  value := value b old component
  strict := strict b old component lower upper

theorem old_fixed (x : O) : value b old component (.inl x) = old.value x := rfl

theorem bound_preserved
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1)))
    (bound : H) (old_bound : ∀ x, R.Weak (old.value x) bound) :
    ∀ x, R.Weak (value b old component x) bound := by
  intro x
  cases x with
  | inl x => exact old_bound x
  | inr x => exact Or.inr (R.lt_weak (upper x) (old_bound (b.separator x.1)))

end AttachmentHeight
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
