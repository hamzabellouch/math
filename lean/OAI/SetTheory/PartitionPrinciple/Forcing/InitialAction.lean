import OAI.SetTheory.PartitionPrinciple.Geometry.TaskSystem

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TaskSystem

open Attachment

universe u

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

theorem initialFreshEq {i j : Task} {y : A}
    {hi : ¬ P.le y (f.datum i).source} {hj : ¬ P.le y (f.datum j).source} (eq : i = j) :
    (⟨i, ⟨y, hi⟩⟩ : f.initial.batch.Fresh) = ⟨j, ⟨y, hj⟩⟩ := by
  cases eq
  rfl

noncomputable def initialRename (g : G) (x : f.initial.batch.Fresh) : f.initial.batch.Fresh :=
  ⟨f.perm g x.1, ⟨x.2.val, by
    change ¬ P.le x.2.val (f.datum (f.perm g x.1)).source
    rw [f.source_invariant]
    exact x.2.property⟩⟩

noncomputable def initialAct (g : G) : A ⊕ f.initial.batch.Fresh → A ⊕ f.initial.batch.Fresh
  | .inl x => .inl ((f.action g).toFun x)
  | .inr x => .inr (f.initialRename g x)

theorem initialRename_left (g : G) (x : f.initial.batch.Fresh) :
    f.initialRename (f.group.inv g) (f.initialRename g x) = x := by
  rcases x with ⟨i, y, hy⟩
  exact f.initialFreshEq (f.perm_left g i)

theorem initialRename_right (g : G) (x : f.initial.batch.Fresh) :
    f.initialRename g (f.initialRename (f.group.inv g) x) = x := by
  rcases x with ⟨i, y, hy⟩
  exact f.initialFreshEq (f.perm_right g i)

theorem initialAct_left (g : G) (x : A ⊕ f.initial.batch.Fresh) :
    f.initialAct (f.group.inv g) (f.initialAct g x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (f.action_left g x)
  | inr x => exact congrArg Sum.inr (f.initialRename_left g x)

theorem initialAct_right (g : G) (x : A ⊕ f.initial.batch.Fresh) :
    f.initialAct g (f.initialAct (f.group.inv g) x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (f.action_right g x)
  | inr x => exact congrArg Sum.inr (f.initialRename_right g x)

theorem initialShadow (g : G) (x : f.initial.batch.Fresh) :
    f.initial.batch.shadow (f.initialRename g x) =
      (f.action g).toFun (f.initial.batch.shadow x) := by
  change (f.action (f.representative (f.perm g x.1))).toFun
    (P.meet x.2.val (f.datum (f.perm g x.1)).source) =
    (f.action g).toFun ((f.action (f.representative x.1)).toFun
      (P.meet x.2.val (f.datum x.1).source))
  rw [f.source_invariant]
  exact (f.ground_compatible g x.1 _ (P.meet_le_right _ _)).symm

theorem initialInside_forward (g : G) {x y : f.initial.batch.Fresh}
    (h : f.initial.batch.Inside x y) :
    f.initial.batch.Inside (f.initialRename g x) (f.initialRename g y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases h with ⟨eq, h⟩
  cases eq
  exact ⟨rfl, h⟩

theorem initialInside_iff (g : G) (x y : f.initial.batch.Fresh) :
    f.initial.batch.Inside (f.initialRename g x) (f.initialRename g y) ↔
      f.initial.batch.Inside x y := by
  constructor
  · intro h
    have h' := f.initialInside_forward (f.group.inv g) h
    rw [f.initialRename_left, f.initialRename_left] at h'
    exact h'
  · exact f.initialInside_forward g

theorem initialOrder (g : G) (x y : A ⊕ f.initial.batch.Fresh) :
    f.initial.batch.extension.le (f.initialAct g x) (f.initialAct g y) ↔
      f.initial.batch.extension.le x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact (f.action g).le_iff x y
    | inr y =>
      change P.le ((f.action g).toFun x) (f.initial.batch.shadow (f.initialRename g y)) ↔ _
      rw [f.initialShadow]
      exact (f.action g).le_iff _ _
  | inr x =>
    cases y with
    | inl y => exact f.filter_covariant g x.1 y
    | inr y =>
      change (f.initial.batch.Inside (f.initialRename g x) (f.initialRename g y) ∨
        (f.datum (f.perm g x.1)).filter.mem (f.initial.batch.shadow (f.initialRename g y))) ↔
        (f.initial.batch.Inside x y ∨ (f.datum x.1).filter.mem (f.initial.batch.shadow y))
      rw [f.initialInside_iff, f.initialShadow, f.filter_covariant]

noncomputable def initialIso (g : G) : MeetIso f.initial.batch.extension f.initial.batch.extension :=
  isoOfOrder (f.initialAct g) (f.initialAct (f.group.inv g))
    (f.initialAct_left g) (f.initialAct_right g) (f.initialOrder g)

theorem initialIso_old (g : G) (x : A) :
    (f.initialIso g).toFun (.inl x) = .inl ((f.action g).toFun x) := rfl

theorem initialIso_one (x : A ⊕ f.initial.batch.Fresh) :
    (f.initialIso f.group.one).toFun x = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (f.action_one x)
  | inr x =>
    rcases x with ⟨i, y, hy⟩
    exact congrArg Sum.inr (f.initialFreshEq (f.perm_one i))

theorem initialIso_mul (g h : G) (x : A ⊕ f.initial.batch.Fresh) :
    (f.initialIso (f.group.mul g h)).toFun x =
      (f.initialIso g).toFun ((f.initialIso h).toFun x) := by
  cases x with
  | inl x => exact congrArg Sum.inl (f.action_mul g h x)
  | inr x =>
    rcases x with ⟨i, y, hy⟩
    exact congrArg Sum.inr (f.initialFreshEq (f.perm_mul g h i))

theorem initial_equivariant (g : G) (i : Task) (x : A) :
    (f.initialIso g).toFun ((f.initial.copy i).toFun x) =
      (f.initial.copy (f.perm g i)).toFun x := by
  classical
  change (f.initialIso g).toFun (f.initial.batch.represent i x) =
    f.initial.batch.represent (f.perm g i) x
  by_cases hx : P.le x (f.datum i).source
  · have hx' : P.le x (f.datum (f.perm g i)).source := by rw [f.source_invariant]; exact hx
    rw [f.initial.batch.represent_old i x hx, f.initial.batch.represent_old (f.perm g i) x hx']
    exact congrArg Sum.inl (f.ground_compatible g i x hx)
  · have hx' : ¬ P.le x (f.datum (f.perm g i)).source := by rw [f.source_invariant]; exact hx
    rw [f.initial.batch.represent_new i x hx, f.initial.batch.represent_new (f.perm g i) x hx']
    rfl

theorem initial_agreement (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (x : A ⊕ f.initial.batch.Fresh) (below : f.initial.batch.extension.le x (.inl v)) :
    (f.initialIso g).toFun x = (f.initialIso h).toFun x := by
  cases x with
  | inl x => exact congrArg Sum.inl (agree x below)
  | inr x =>
    rcases x with ⟨i, y, hy⟩
    exact congrArg Sum.inr (f.initialFreshEq (f.positive_perms_agree g h v agree i below))

noncomputable def initialInputs : Inputs f.initial.batch Task where
  source i := (f.datum i).source
  previous := f.initial.copy
  representative i := f.initialIso (f.representative i)
  agree := f.initial.copy_agrees_on_base

noncomputable def initialSymmetry (g : G) : TaskSymmetry f.initialInputs where
  perm := f.perm g
  inverse := f.perm (f.group.inv g)
  left_inverse := f.perm_left g
  right_inverse := f.perm_right g
  current := f.initialIso g
  source := f.source_invariant g
  intertwine := f.initial_equivariant g

theorem initial_negative (i : Task) (v : A) (negative : ¬ (f.datum i).filter.mem v) :
    f.initial.batch.extension.le
      (f.initial.batch.extension.meet ((f.initial.copy i).toFun f.top) (.inl v))
      ((f.initial.copy i).toFun (f.datum i).source) := by
  have src := f.initial.copy_agrees_on_base i (f.datum i).source (P.refl _)
  change f.initial.batch.extension.le
    (f.initial.batch.extension.meet (f.initial.batch.represent i f.top) (.inl v)) _
  rw [f.initial.batch.represent_new i f.top (f.source_proper i), src,
    f.initial.batch.shadow_meet_eq ⟨i, ⟨f.top, f.source_proper i⟩⟩ v negative]
  have hs := f.initial.batch.cap_shadow i f.top f.greatest (f.source_proper i)
  change f.initial.batch.shadow ⟨i, ⟨f.top, f.source_proper i⟩⟩ = _ at hs
  rw [hs]
  exact P.meet_le_left _ _

end PartitionPilot.Compression.RecursiveMaps.TaskSystem

end

end OAI
