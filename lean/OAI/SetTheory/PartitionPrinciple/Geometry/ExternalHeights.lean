import OAI.SetTheory.PartitionPrinciple.Forcing.FixedTop

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open RationalHeights
universe u v

namespace LinearHeightOrder
variable {Column : Type u} {Coord : Type v}

theorem first_weak (C : LinearHeightOrder Column) (D : LinearHeightOrder Coord)
    {x y : Column × Coord} (lower : (C.lex D).Weak x y) : C.Weak x.1 y.1 := by
  rcases lower with eq | lower | ⟨eq, _⟩
  · exact Or.inl (congrArg Prod.fst eq)
  · exact Or.inr lower
  · exact Or.inl eq

end LinearHeightOrder

structure ColumnRoom {Column : Type v} (C : LinearHeightOrder Column) (old : Column) where
  column : Nat → Column
  increasing : ∀ n, C.lt (column n) (column (n + 1))
  starts_above : C.lt old (column 0)
  cap : Column
  below_cap : ∀ n, C.lt (column n) cap

namespace FixedTop
variable {A : Type u} {H : Type v} {P : MeetOrder A} {R : HeightOrder H}
    (height : StrictHeight P R) (topValue : H)
    (above : ∀ x, R.lt (height.value x) topValue)

def heightValue : Option A → H
  | none => topValue
  | some x => height.value x

def extendHeight : StrictHeight (order P) R where
  value := heightValue height topValue
  strict x y lower different := by
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (different rfl)
      | some y => exact False.elim lower
    | some x =>
      cases y with
      | none => exact above x
      | some y => exact height.strict x y lower (fun eq => different (congrArg some eq))

theorem extendHeight_countable (countable : CountableRange height.value) :
    CountableRange (extendHeight height topValue above).value := by
  rcases countable with ⟨oldCode, equal⟩
  let code : Option A → Nat
    | none => 0
    | some x => oldCode x + 1
  refine ⟨code, ?_⟩
  intro x y eq
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => change 0 = oldCode y + 1 at eq; omega
  | some x =>
    cases y with
    | none => change oldCode x + 1 = 0 at eq; omega
    | some y => exact equal x y (by change oldCode x + 1 = oldCode y + 1 at eq; omega)

end FixedTop

namespace TileRequests.Family

open CosetGeometry
variable {A J R : Type u} [Group J] {P : MeetOrder A}
    {Column : Type v} (f : Family P R) (a : OrderAction J P)
    (C : LinearHeightOrder Column) (seed : StrictHeight P (lexOrder C).toHeightOrder)
    (countable : CountableRange seed.value)
    (room : ColumnRoom C (seed.value f.top).1)

noncomputable def localHeight : (v : TileStars.Vertex J f.Letters R) →
    StrictHeight (f.localOrder v) Rational.order.toHeightOrder
  | .inl _ => Classical.choose (rational_assignment (lexOrder C) seed f.top countable)
  | .inr c => (f.request c.2).rationalHeight f.top f.greatest (lexOrder C) seed countable

theorem seed_column_bound (x : A) : C.lt (seed.value x).1 (room.column 0) :=
  C.weak_lt (C.first_weak Rational.order.toLinearHeightOrder (seed.mono (f.greatest x)))
    room.starts_above

noncomputable def gluedHeight : StrictHeight (f.gluedOrder a) (lexOrder C).toHeightOrder :=
  (f.diagram a).scheme.externalHeight C room.column room.increasing seed
    (f.seed_column_bound C seed room) (f.localHeight C seed countable)

theorem gluedHeight_original (x : A) :
    (f.gluedHeight a C seed countable room).value ((f.copy a 1).toFun x) = seed.value x := by
  rw [f.copy_one]
  exact (f.diagram a).scheme.externalHeight_original C room.column room.increasing seed
    (f.seed_column_bound C seed room) (f.localHeight C seed countable) x

theorem gluedHeight_countable : CountableRange (f.gluedHeight a C seed countable room).value :=
  (f.diagram a).scheme.externalHeight_countable C room.column room.increasing seed
    (f.seed_column_bound C seed room) (f.localHeight C seed countable) countable

theorem gluedHeight_column_bound (x : f.Node a) :
    C.lt ((f.gluedHeight a C seed countable room).value x).1 room.cap :=
  (f.diagram a).scheme.externalHeight_column_bound C room.column room.increasing seed
    (f.seed_column_bound C seed room) (f.localHeight C seed countable) room.cap room.below_cap x

noncomputable def extensionHeight : StrictHeight (f.extensionOrder a) (lexOrder C).toHeightOrder :=
  FixedTop.extendHeight (f.gluedHeight a C seed countable room) (room.cap, zero)
    (fun x => Or.inl (f.gluedHeight_column_bound a C seed countable room x))

theorem extensionHeight_original (x : A) :
    (f.extensionHeight a C seed countable room).value ((f.extensionCopy a 1).toFun x) =
      seed.value x := f.gluedHeight_original a C seed countable room x

theorem extensionHeight_countable :
    CountableRange (f.extensionHeight a C seed countable room).value :=
  FixedTop.extendHeight_countable _ _ _ (f.gluedHeight_countable a C seed countable room)

theorem extensionHeight_top :
    (f.extensionHeight a C seed countable room).value none = (room.cap, zero) := rfl

theorem extensionHeight_bounded (x : f.Extension a) :
    (lexOrder C).Weak ((f.extensionHeight a C seed countable room).value x) (room.cap, zero) :=
  (f.extensionHeight a C seed countable room).mono (f.extension_greatest a x)

include countable in

theorem external_height_extension :
    ∃ height : StrictHeight (f.extensionOrder a) (lexOrder C).toHeightOrder,
      (∀ x, height.value ((f.extensionCopy a 1).toFun x) = seed.value x) ∧
      CountableRange height.value ∧ height.value none = (room.cap, zero) ∧
      (∀ x, (lexOrder C).Weak (height.value x) (room.cap, zero)) :=
  ⟨f.extensionHeight a C seed countable room,
    f.extensionHeight_original a C seed countable room,
    f.extensionHeight_countable a C seed countable room,
    f.extensionHeight_top a C seed countable room,
    f.extensionHeight_bounded a C seed countable room⟩

end TileRequests.Family

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
