import OAI.SetTheory.PartitionPrinciple.Transfinite.MainBirthOrigins

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage

open CosetGeometry RationalHeights
universe u

def initialOrder : MeetOrder (ULift.{u} Bool) where
  le x y := x.down ≤ y.down
  meet x y := ⟨min x.down y.down⟩
  refl _ := le_rfl
  trans := le_trans
  antisymm hxy hyx := ULift.ext _ _ (le_antisymm hxy hyx)
  meet_le_left x y := min_le_left x.down y.down
  meet_le_right x y := min_le_right x.down y.down
  le_meet := le_min

noncomputable def initialHeight :
    StrictHeight initialOrder.{u} (lexOrder CountableColumns.order).toHeightOrder where
  value x := (CountableColumns.natural 0, if x.down then one else zero)
  strict x y lower different := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    cases x <;> cases y
    · exact False.elim (different rfl)
    · exact Or.inr ⟨rfl, RationalHeights.zero_lt_one⟩
    · exact False.elim ((by decide : ¬ (true : Bool) ≤ false) lower)
    · exact False.elim (different rfl)

theorem initialHeight_countable : CountableRange initialHeight.{u}.value := by
  rcases exists_injective_nat (ULift.{u} Bool) with ⟨code, injective⟩
  exact ⟨code, fun x y eq => congrArg initialHeight.value (injective eq)⟩

noncomputable def initial : MainStage.{u} where
  Point := ULift.{u} Bool
  order := initialOrder
  Actor := Equiv.Perm (ULift.{u} Unit)
  action := {
    iso _ := identityIso initialOrder
    one _ := rfl
    mul _ _ _ := rfl }
  bottom := ⟨false⟩
  least x := Bool.false_le x.down
  top := ⟨true⟩
  greatest x := Bool.le_true x.down
  height := initialHeight
  countable_height := initialHeight_countable

theorem initial_two_points (x : initial.{u}.Point) : x = initial.bottom ∨ x = initial.top := by
  rcases x with ⟨x⟩
  cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem initial_bottom_ne_top : initial.{u}.bottom ≠ initial.top := by
  intro eq
  have bad := congrArg ULift.down eq
  exact Bool.false_ne_true bad

theorem initial_action_trivial (g : initial.{u}.Actor) (x : initial.Point) :
    (initial.action.iso g).toFun x = x := rfl

theorem initial_group_trivial (g : initial.{u}.Actor) : g = 1 := by
  apply Equiv.ext
  intro x
  exact Subsingleton.elim _ _

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
