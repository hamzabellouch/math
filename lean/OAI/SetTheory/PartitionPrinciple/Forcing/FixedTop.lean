import OAI.SetTheory.PartitionPrinciple.Definability.ExternalRealization

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.FixedTop

open CosetGeometry
universe u
variable {A J : Type u} (P : MeetOrder A)

def Le : Option A → Option A → Prop
  | _, none => True
  | none, some _ => False
  | some x, some y => P.le x y

def meet : Option A → Option A → Option A
  | none, y => y
  | x, none => x
  | some x, some y => some (P.meet x y)

def order : MeetOrder (Option A) where
  le := Le P
  meet := meet P
  refl x := by
    cases x with
    | none => trivial
    | some x => exact P.refl x
  trans {x y z} hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp only [Le] at *
    exact P.trans hxy hyz
  antisymm {x y} hxy hyx := by
    cases x <;> cases y <;> simp only [Le] at *
    exact congrArg some (P.antisymm hxy hyx)
  meet_le_left x y := by
    cases x <;> cases y <;> simp only [meet, Le]
    · exact P.refl _
    · exact P.meet_le_left _ _
  meet_le_right x y := by
    cases x <;> cases y <;> simp only [meet, Le]
    · exact P.refl _
    · exact P.meet_le_right _ _
  le_meet {x y z} hxy hxz := by
    cases x <;> cases y <;> cases z <;> simp only [meet, Le] at *
    all_goals first | exact hxy | exact hxz | exact P.le_meet hxy hxz

def embedding : IdealEmbedding P (order P) where
  toFun := some
  le_iff _ _ := Iff.rfl
  map_meet _ _ := rfl
  ideal x z h := by
    cases z with
    | none => exact False.elim h
    | some z => exact ⟨z, rfl⟩

theorem strict_top (x : A) : (order P).le ((embedding P).toFun x) none ∧
    ¬ (order P).le none ((embedding P).toFun x) := ⟨True.intro, id⟩

theorem greatest (x : Option A) : (order P).le x none := by
  cases x <;> exact True.intro

theorem no_new_below (x : A) (z : Option A) (h : (order P).le z ((embedding P).toFun x)) :
    ∃ y, (embedding P).toFun y = z := (embedding P).ideal x z h

variable [Group J] (a : OrderAction J P)

def act (g : J) : Option A → Option A
  | none => none
  | some x => some ((a.iso g).toFun x)

def actionIso (g : J) : MeetIso (order P) (order P) where
  toFun := act P a g
  le_iff x y := by
    cases x <;> cases y <;> simp only [act, order, Le]
    exact (a.iso g).le_iff _ _
  map_meet x y := by
    cases x <;> cases y <;> simp only [act, order, meet]
    exact congrArg some ((a.iso g).map_meet _ _)
  inverse
    | none => none
    | some x => some ((a.iso g).inverse x)
  left_inverse x := by
    cases x with
    | none => rfl
    | some x => exact congrArg some ((a.iso g).left_inverse x)
  right_inverse x := by
    cases x with
    | none => rfl
    | some x => exact congrArg some ((a.iso g).right_inverse x)

def action : OrderAction J (order P) where
  iso := actionIso P a
  one x := by
    cases x with
    | none => rfl
    | some x => exact congrArg some (a.one x)
  mul g h x := by
    cases x with
    | none => rfl
    | some x => exact congrArg some (a.mul g h x)

theorem fixes_top (g : J) : ((action P a).iso g).toFun none = none := rfl

theorem extends_action (g : J) (x : A) :
    ((action P a).iso g).toFun ((embedding P).toFun x) =
      (embedding P).toFun ((a.iso g).toFun x) := rfl

end PartitionPilot.Compression.RecursiveMaps.FixedTop

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

def Extension := Option (f.Node a)
noncomputable def extensionOrder : MeetOrder (f.Extension a) := FixedTop.order (f.gluedOrder a)
noncomputable def extensionAction : OrderAction (External J f.Letters) (f.extensionOrder a) :=
  FixedTop.action (f.gluedOrder a) (f.externalAction a)
noncomputable def extensionCopy (w : External J f.Letters) : IdealEmbedding P (f.extensionOrder a) :=
  (f.copy a w).comp (FixedTop.embedding (f.gluedOrder a))

theorem extension_greatest (x : f.Extension a) : (f.extensionOrder a).le x none :=
  FixedTop.greatest (f.gluedOrder a) x

theorem extension_strict_top (w : External J f.Letters) (x : A) :
    (f.extensionOrder a).le ((f.extensionCopy a w).toFun x) none ∧
      ¬ (f.extensionOrder a).le none ((f.extensionCopy a w).toFun x) :=
  FixedTop.strict_top (f.gluedOrder a) ((f.copy a w).toFun x)

theorem extension_fixes_top (g : External J f.Letters) :
    ((f.extensionAction a).iso g).toFun none = none := rfl

theorem extensionAction_copy (g w : External J f.Letters) (x : A) :
    ((f.extensionAction a).iso g).toFun ((f.extensionCopy a w).toFun x) =
      (f.extensionCopy a (g * w)).toFun x :=
  congrArg some (f.externalAction_copy a g w x)

theorem extension_extends_old (j : J) (x : A) :
    ((f.extensionAction a).iso (old J f.Letters j)).toFun ((f.extensionCopy a 1).toFun x) =
      (f.extensionCopy a 1).toFun ((a.iso j).toFun x) :=
  congrArg some (f.extends_old_action a j x)

theorem extensionCopy_principal (w : External J f.Letters) (z : f.Extension a) :
    (f.extensionOrder a).le z ((f.extensionCopy a w).toFun f.top) ↔
      ∃ x, (f.extensionCopy a w).toFun x = z :=
  (f.extensionCopy a w).principal f.top f.greatest z

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
