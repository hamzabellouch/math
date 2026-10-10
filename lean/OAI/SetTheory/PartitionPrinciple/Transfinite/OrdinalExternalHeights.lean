import OAI.SetTheory.PartitionPrinciple.Geometry.ExternalHeights

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open RationalHeights
open scoped Cardinal Ordinal
universe u

namespace CountableColumns

def Column := {o : Ordinal.{0} // o.card ≤ Cardinal.aleph0}

theorem membership_iff (o : Ordinal.{0}) :
    o.card ≤ Cardinal.aleph0 ↔ o < (Cardinal.aleph 1).ord := by
  rw [Cardinal.lt_ord, ← Cardinal.succ_aleph0, Order.lt_succ_iff]

noncomputable def order : LinearHeightOrder Column where
  lt x y := x.val < y.val
  irrefl x := lt_irrefl x.val
  trans := lt_trans
  compare x y := by
    rcases lt_trichotomy x.val y.val with lower | eq | lower
    · exact Or.inl lower
    · exact Or.inr (Or.inl (Subtype.ext eq))
    · exact Or.inr (Or.inr lower)

def add (a b : Column) : Column :=
  ⟨a.val + b.val, by rw [Ordinal.card_add]; exact Cardinal.add_le_aleph0.mpr ⟨a.property, b.property⟩⟩

def natural (n : Nat) : Column :=
  ⟨n, by rw [Ordinal.card_nat]; exact Cardinal.natCast_le_aleph0⟩

def omega : Column := ⟨Ordinal.omega0, by rw [Ordinal.card_omega0]⟩

def start (old : Column) : Column := add old (natural 1)
def layer (old : Column) (n : Nat) : Column := add (start old) (natural n)
def cap (old : Column) : Column := add (start old) omega

theorem layer_increasing (old : Column) (n : Nat) :
    order.lt (layer old n) (layer old (n + 1)) := by
  change (start old).val + (n : Ordinal) < (start old).val + ((n + 1 : Nat) : Ordinal)
  exact (add_lt_add_iff_left (start old).val).2 (Nat.cast_lt.mpr (Nat.lt_succ_self n))

theorem starts_above (old : Column) : order.lt old (layer old 0) := by
  change old.val < (old.val + (1 : Nat)) + (0 : Nat)
  simpa only [Nat.cast_zero, Nat.cast_one, add_zero, Order.succ_eq_add_one] using
    (Order.lt_succ old.val)

theorem below_cap (old : Column) (n : Nat) : order.lt (layer old n) (cap old) :=
  add_lt_add_right (Ordinal.natCast_lt_omega0 n) (start old).val

noncomputable def room (old : Column) : ColumnRoom order old where
  column := layer old
  increasing := layer_increasing old
  starts_above := starts_above old
  cap := cap old
  below_cap := below_cap old

end CountableColumns

namespace TileRequests.Family

open CosetGeometry CountableColumns
variable {A J R : Type u} [Group J] {P : MeetOrder A}
    (f : Family P R) (a : OrderAction J P)
    (seed : StrictHeight P (lexOrder CountableColumns.order).toHeightOrder)
    (countable : CountableRange seed.value)

noncomputable def ordinalExtensionHeight :
    StrictHeight (f.extensionOrder a) (lexOrder CountableColumns.order).toHeightOrder :=
  f.extensionHeight a CountableColumns.order seed countable (room (seed.value f.top).1)

theorem ordinalExtensionHeight_original (x : A) :
    (f.ordinalExtensionHeight a seed countable).value ((f.extensionCopy a 1).toFun x) =
      seed.value x :=
  f.extensionHeight_original a CountableColumns.order seed countable (room (seed.value f.top).1) x

theorem ordinalExtensionHeight_countable :
    CountableRange (f.ordinalExtensionHeight a seed countable).value :=
  f.extensionHeight_countable a CountableColumns.order seed countable (room (seed.value f.top).1)

theorem ordinalExtensionHeight_top :
    (f.ordinalExtensionHeight a seed countable).value none = (cap (seed.value f.top).1, zero) := rfl

include countable in

theorem ordinal_external_height_extension :
    ∃ height : StrictHeight (f.extensionOrder a) (lexOrder CountableColumns.order).toHeightOrder,
      (∀ x, height.value ((f.extensionCopy a 1).toFun x) = seed.value x) ∧
      CountableRange height.value ∧
      height.value none = (cap (seed.value f.top).1, zero) ∧
      (∀ x, (lexOrder CountableColumns.order).Weak
        (height.value x) (cap (seed.value f.top).1, zero)) :=
  f.external_height_extension a CountableColumns.order seed countable (room (seed.value f.top).1)

end TileRequests.Family

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
