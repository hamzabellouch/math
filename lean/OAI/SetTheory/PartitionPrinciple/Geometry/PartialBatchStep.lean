import OAI.SetTheory.PartitionPrinciple.Forcing.FixedTop

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family

universe u
variable {A I : Type u} {P : MeetOrder A} (b : PrincipalBatch.Family P I)

def Present (U : I → Prop) : b.Node → Prop
  | .inl _ => True
  | .inr x => U x.1

theorem present_down (U : I → Prop) {x y : b.Node} (hy : b.Present U y)
    (hxy : b.extension.le x y) : b.Present U x := by
  cases x with
  | inl x => exact True.intro
  | inr x =>
    cases y with
    | inl y => exact False.elim hxy
    | inr y =>
      rcases hxy with ⟨eq, _⟩ | impossible
      · change U x.1
        change U y.1 at hy
        exact eq.symm ▸ hy
      · exact False.elim impossible

def Cutoff (U : I → Prop) := {x : b.Node // b.Present U x}

noncomputable def cutoffOrder (U : I → Prop) : MeetOrder (b.Cutoff U) where
  le x y := b.extension.le x.val y.val
  meet x y := ⟨b.extension.meet x.val y.val,
    b.present_down U x.property (b.extension.meet_le_left _ _)⟩
  refl x := b.extension.refl x.val
  trans := b.extension.trans
  antisymm hxy hyx := Subtype.ext (b.extension.antisymm hxy hyx)
  meet_le_left x y := b.extension.meet_le_left x.val y.val
  meet_le_right x y := b.extension.meet_le_right x.val y.val
  le_meet := b.extension.le_meet

noncomputable def cutoffEmbedding (U : I → Prop) : IdealEmbedding (b.cutoffOrder U) b.extension where
  toFun := Subtype.val
  le_iff _ _ := Iff.rfl
  map_meet _ _ := rfl
  ideal x y h := ⟨⟨y, b.present_down U x.property h⟩, rfl⟩

noncomputable def cutoffOld (U : I → Prop) : IdealEmbedding P (b.cutoffOrder U) where
  toFun x := ⟨b.old.toFun x, True.intro⟩
  le_iff x y := b.old.le_iff x y
  map_meet x y := Subtype.ext (b.old.map_meet x y)
  ideal x y h := by
    rcases b.old.ideal x y.val h with ⟨z, eq⟩
    exact ⟨z, Subtype.ext eq⟩

theorem present_tile (U : I → Prop) (i : I) (hi : U i) (x : b.Space i) :
    b.Present U ((b.tile i).toFun x) := by
  change b.Present U (b.componentMap i ((b.glue i).represent x))
  cases (b.glue i).represent x with
  | inl y => exact True.intro
  | inr y => exact hi

noncomputable def cutoffTile (U : I → Prop) (i : I) (hi : U i) :
    IdealEmbedding (b.order i) (b.cutoffOrder U) where
  toFun x := ⟨(b.tile i).toFun x, b.present_tile U i hi x⟩
  le_iff x y := (b.tile i).le_iff x y
  map_meet x y := Subtype.ext ((b.tile i).map_meet x y)
  ideal x y h := by
    rcases (b.tile i).ideal x y.val h with ⟨z, eq⟩
    exact ⟨z, Subtype.ext eq⟩

theorem present_mono {U V : I → Prop} (h : ∀ i, U i → V i) {x : b.Node}
    (hx : b.Present U x) : b.Present V x := by
  cases x with
  | inl x => exact True.intro
  | inr x => exact h x.1 hx

noncomputable def cutoffInclusion {U V : I → Prop} (h : ∀ i, U i → V i) :
    IdealEmbedding (b.cutoffOrder U) (b.cutoffOrder V) where
  toFun x := ⟨x.val, b.present_mono h x.property⟩
  le_iff _ _ := Iff.rfl
  map_meet _ _ := rfl
  ideal x y lower := ⟨⟨y.val, b.present_down U x.property lower⟩, rfl⟩

theorem cutoffInclusion_coherent {U V W : I → Prop} (hUV : ∀ i, U i → V i)
    (hVW : ∀ i, V i → W i) (x : b.Cutoff U) :
    (b.cutoffInclusion hVW).toFun ((b.cutoffInclusion hUV).toFun x) =
      (b.cutoffInclusion (fun i hi => hVW i (hUV i hi))).toFun x := rfl

theorem cutoff_no_new_below (U : I → Prop) (x : b.Cutoff U) (y : b.Node)
    (lower : b.extension.le y x.val) : ∃ z : b.Cutoff U, z.val = y :=
  (b.cutoffEmbedding U).ideal x y lower

theorem cutoff_cover (U : I → Prop) (x : b.Cutoff U) :
    (∃ a, (b.cutoffOld U).toFun a = x) ∨
      ∃ i, ∃ hi : U i, ∃ y, (b.cutoffTile U i hi).toFun y = x := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr x =>
    refine Or.inr ⟨x.1, hx, x.2.val, ?_⟩
    apply Subtype.ext
    exact congrArg (b.componentMap x.1) ((b.glue x.1).represent_new x.2.val x.2.property)

end PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family



namespace PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family

open Attachment
universe u
variable {A I : Type u} {P : MeetOrder A} (b : PrincipalBatch.Family P I)

theorem outside_greatest_part (U : I → Prop) (i : I) (outside : ¬ U i)
    (x : (b.glue i).Fresh) (y : b.Cutoff U) :
    b.extension.le y.val (.inr ⟨i, x⟩) ↔
      b.extension.le y.val (b.old.toFun ((b.glue i).shadow x.val)) := by
  rcases y with ⟨y, hy⟩
  cases y with
  | inl y => exact Iff.rfl
  | inr y =>
    constructor
    · intro h
      have different : y.1 ≠ i := by
        intro eq
        change U y.1 at hy
        exact outside (eq ▸ hy)
      exact False.elim (b.different_fresh_incomparable y ⟨i, x⟩ different h)
    · exact False.elim

theorem outside_meet (U : I → Prop) (i : I) (outside : ¬ U i)
    (x : (b.glue i).Fresh) (y : b.Cutoff U) :
    b.extension.meet (.inr ⟨i, x⟩) y.val =
      b.extension.meet (b.old.toFun ((b.glue i).shadow x.val)) y.val := by
  apply b.extension.antisymm
  · let z : b.Cutoff U := ⟨b.extension.meet (.inr ⟨i, x⟩) y.val,
      b.present_down U y.property (b.extension.meet_le_right _ _)⟩
    exact b.extension.le_meet
      ((b.outside_greatest_part U i outside x z).mp (b.extension.meet_le_left _ _))
      (b.extension.meet_le_right _ _)
  · exact b.extension.le_meet
      (b.extension.trans (b.extension.meet_le_left _ _)
        ((b.fresh_greatest_old_part ⟨i, x⟩ _).mpr (P.refl _)))
      (b.extension.meet_le_right _ _)

theorem present_unselected_tile (U : I → Prop) (i : I) (outside : ¬ U i) (x : b.Space i) :
    b.Present U ((b.tile i).toFun x) ↔ (b.order i).le x (b.glue i).rightAnchor := by
  classical
  change b.Present U (b.componentMap i ((b.glue i).represent x)) ↔ _
  by_cases hx : (b.order i).le x (b.glue i).rightAnchor
  · rw [(b.glue i).represent_old x hx]
    exact ⟨fun _ => hx, fun _ => True.intro⟩
  · rw [(b.glue i).represent_new x hx]
    exact ⟨fun hi => False.elim (outside hi), fun h => False.elim (hx h)⟩

def addComponent (U : I → Prop) (i : I) (j : I) : Prop := U j ∨ j = i

noncomputable def stepInput (U : I → Prop) (i : I) :
    PrincipalAmalgamation.Input (b.cutoffOrder U) (b.order i) where
  leftAnchor := (b.cutoffOld U).toFun (b.glue i).leftAnchor
  rightAnchor := (b.glue i).rightAnchor
  overlap := RootedGluing.chainIso (b.glue i).overlap
    ((b.cutoffOld U).principalIso (b.glue i).leftAnchor)

def stepMap (U : I → Prop) (i : I) : (b.stepInput U i).Node → b.Cutoff (addComponent U i)
  | .inl x => ⟨x.val, b.present_mono (fun _ h => Or.inl h) x.property⟩
  | .inr x => ⟨.inr ⟨i, x⟩, Or.inr rfl⟩

theorem stepMap_le (U : I → Prop) (i : I) (outside : ¬ U i) (x y : (b.stepInput U i).Node) :
    (b.cutoffOrder (addComponent U i)).le (b.stepMap U i x) (b.stepMap U i y) ↔
      (b.stepInput U i).order.le x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact Iff.rfl
    | inr y => exact b.outside_greatest_part U i outside y x
  | inr x =>
    cases y with
    | inl y =>
      exact ⟨fun h => False.elim (outside (b.present_down U y.property h)), False.elim⟩
    | inr y => exact b.componentMap_le i (.inr x) (.inr y)

theorem stepMap_surjective (U : I → Prop) (i : I) (y : b.Cutoff (addComponent U i)) :
    ∃ x, b.stepMap U i x = y := by
  rcases y with ⟨y, hy⟩
  cases y with
  | inl y => exact ⟨.inl ⟨.inl y, True.intro⟩, rfl⟩
  | inr y =>
    rcases y with ⟨j, y⟩
    rcases hy with hj | rfl
    · exact ⟨.inl ⟨.inr ⟨j, y⟩, hj⟩, rfl⟩
    · exact ⟨.inr y, rfl⟩

noncomputable def stepEmbedding (U : I → Prop) (i : I) (outside : ¬ U i) :
    IdealEmbedding (b.stepInput U i).order (b.cutoffOrder (addComponent U i)) :=
  IdealEmbedding.ofOrderMap (b.stepMap U i) (b.stepMap_le U i outside)
    (fun _ y _ => b.stepMap_surjective U i y)

noncomputable def stepIso (U : I → Prop) (i : I) (outside : ¬ U i) :
    MeetIso (b.stepInput U i).order (b.cutoffOrder (addComponent U i)) where
  toMeetEmbedding := (b.stepEmbedding U i outside).toMeetEmbedding
  inverse y := Classical.choose (b.stepMap_surjective U i y)
  right_inverse y := Classical.choose_spec (b.stepMap_surjective U i y)
  left_inverse x := embedding_injective (b.stepEmbedding U i outside).toMeetEmbedding
    (Classical.choose_spec (b.stepMap_surjective U i (b.stepMap U i x)))

theorem stepIso_old (U : I → Prop) (i : I) (outside : ¬ U i) (x : b.Cutoff U) :
    (b.stepIso U i outside).toFun ((b.stepInput U i).left.toFun x) =
      (b.cutoffInclusion (fun _ h => Or.inl h : ∀ j, U j → addComponent U i j)).toFun x := rfl

theorem stepIso_tile (U : I → Prop) (i : I) (outside : ¬ U i) (x : b.Space i) :
    (b.stepIso U i outside).toFun ((b.stepInput U i).right.toFun x) =
      (b.cutoffTile (addComponent U i) i (Or.inr rfl)).toFun x := by
  classical
  apply Subtype.ext
  change (b.stepMap U i ((b.stepInput U i).represent x)).val =
    b.componentMap i ((b.glue i).represent x)
  by_cases hx : (b.order i).le x (b.glue i).rightAnchor
  · rw [(b.stepInput U i).represent_old x hx, (b.glue i).represent_old x hx]
    rfl
  · rw [(b.stepInput U i).represent_new x hx, (b.glue i).represent_new x hx]
    rfl

end PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family

end

end OAI
