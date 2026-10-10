import OAI.SetTheory.PartitionPrinciple.Forcing.InitialAction

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u

structure CompressionStage {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) where
  Old : Type u
  Components : Type u
  oldOrder : MeetOrder Old
  batch : Templates.{u,u,u} oldOrder Components
  original : MeetEmbedding P oldOrder
  inputs : Inputs batch Task
  source_original : ∀ i, inputs.source i = original.toFun (f.datum i).source
  top : ∀ x, oldOrder.le x (original.toFun f.top)
  symmetry : G → TaskSymmetry inputs
  perm_eq : ∀ g i, (symmetry g).perm i = f.perm g i
  representatives : ∀ i x, (symmetry (f.representative i)).current.toFun x =
    (inputs.representative i).toFun x
  action_one : ∀ x, (symmetry f.group.one).current.toFun x = x
  action_mul : ∀ g h x, (symmetry (f.group.mul g h)).current.toFun x =
    (symmetry g).current.toFun ((symmetry h).current.toFun x)
  action_original : ∀ g x, (symmetry g).current.toFun (.inl (original.toFun x)) =
    .inl (original.toFun ((f.action g).toFun x))
  agreement : ∀ g h v,
    (∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x) →
    ∀ x, batch.extension.le x (.inl (original.toFun v)) →
      (symmetry g).current.toFun x = (symmetry h).current.toFun x
  negative : ∀ i v, ¬ (f.datum i).filter.mem v →
    batch.extension.le
      (batch.extension.meet ((inputs.previous i).toFun (original.toFun f.top))
        (.inl (original.toFun v)))
      ((inputs.previous i).toFun (inputs.source i))

namespace CompressionStage

variable {A G Task Label : Type u} {P : MeetOrder A} {f : TaskSystem P G Task Label}
    (s : CompressionStage f)

theorem compatible (g : G) (i : Task) (x : s.Old ⊕ s.batch.Fresh)
    (hx : s.batch.extension.le x (.inl (s.inputs.source i))) :
    (s.symmetry g).current.toFun ((s.inputs.representative i).toFun x) =
      (s.inputs.representative ((s.symmetry g).perm i)).toFun x := by
  have ground : ∀ y, P.le y (f.datum i).source →
      (f.action (f.group.mul g (f.representative i))).toFun y =
        (f.action (f.representative (f.perm g i))).toFun y := by
    intro y hy
    rw [f.action_mul]
    exact f.ground_compatible g i y hy
  rw [s.source_original] at hx
  have current := s.agreement (f.group.mul g (f.representative i))
    (f.representative (f.perm g i)) (f.datum i).source ground x hx
  rw [s.action_mul, s.representatives, s.representatives] at current
  rw [s.perm_eq]
  exact current

noncomputable def nextInputs : Inputs s.inputs.nextBatch Task :=
  s.inputs.nextInputs (fun i => s.symmetry (f.representative i)) s.representatives

noncomputable def nextAction (g : G) : TaskSymmetry s.nextInputs :=
  s.inputs.nextSymmetry (fun i => s.symmetry (f.representative i)) s.representatives
    (s.symmetry g) (s.compatible g)

theorem next_action_one (x : (s.Old ⊕ s.batch.Fresh) ⊕ s.inputs.nextBatch.Fresh) :
    (s.nextAction f.group.one).current.toFun x = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.action_one x)
  | inr x =>
    rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
    apply congrArg Sum.inr
    exact TaskSymmetry.fresh_task_eq ((s.perm_eq f.group.one i).trans (f.perm_one i))

theorem next_action_mul (g h : G)
    (x : (s.Old ⊕ s.batch.Fresh) ⊕ s.inputs.nextBatch.Fresh) :
    (s.nextAction (f.group.mul g h)).current.toFun x =
      (s.nextAction g).current.toFun ((s.nextAction h).current.toFun x) := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.action_mul g h x)
  | inr x =>
    rcases x with ⟨⟨i, ⟨k, eligible⟩⟩, ⟨y, outside⟩⟩
    apply congrArg Sum.inr
    apply TaskSymmetry.fresh_task_eq
    change (s.symmetry (f.group.mul g h)).perm i = (s.symmetry g).perm ((s.symmetry h).perm i)
    rw [s.perm_eq, s.perm_eq, s.perm_eq, f.perm_mul]

theorem next_action_original (g : G) (x : A) :
    (s.nextAction g).current.toFun (.inl (.inl (s.original.toFun x))) =
      .inl (.inl (s.original.toFun ((f.action g).toFun x))) :=
  congrArg Sum.inl (s.action_original g x)

theorem next_agreement (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (x : (s.Old ⊕ s.batch.Fresh) ⊕ s.inputs.nextBatch.Fresh)
    (below : s.inputs.nextBatch.extension.le x (.inl (.inl (s.original.toFun v)))) :
    (s.nextAction g).current.toFun x = (s.nextAction h).current.toFun x := by
  apply TaskDatum.successor_agreement (s.symmetry g) (s.symmetry h) s.original
    f.datum f.faithful f.geometry (f.action g) (f.action h)
    (fun i => (congrArg f.datum (s.perm_eq g i)).trans (f.transport g i))
    (fun i => (congrArg f.datum (s.perm_eq h i)).trans (f.transport h i))
    (s.original.toFun f.top) s.top v (fun i => s.negative i v)
    agree (s.agreement g h v agree) x below

theorem next_negative (i : Task) (v : A) (negative : ¬ (f.datum i).filter.mem v) :
    s.inputs.nextBatch.extension.le
      (s.inputs.nextBatch.extension.meet
        ((s.nextInputs.previous i).toFun (.inl (s.original.toFun f.top)))
        (.inl (.inl (s.original.toFun v))))
      ((s.nextInputs.previous i).toFun (s.nextInputs.source i)) := by
  have h := (s.inputs.nextBatch.oldEmbedding.le_iff _ _).mpr (s.negative i v negative)
  have hm := s.inputs.nextBatch.oldEmbedding.map_meet
    ((s.inputs.previous i).toFun (s.original.toFun f.top)) (.inl (s.original.toFun v))
  rw [hm] at h
  exact h

noncomputable def next : CompressionStage f where
  Old := s.Old ⊕ s.batch.Fresh
  Components := s.inputs.Labels
  oldOrder := s.batch.extension
  batch := s.inputs.nextBatch
  original := compose s.original s.batch.oldEmbedding
  inputs := s.nextInputs
  source_original i := congrArg Sum.inl (s.source_original i)
  top := s.batch.greatest_preserved (s.original.toFun f.top) s.top
  symmetry := s.nextAction
  perm_eq := s.perm_eq
  representatives _ _ := rfl
  action_one := s.next_action_one
  action_mul := s.next_action_mul
  action_original := s.next_action_original
  agreement := s.next_agreement
  negative := s.next_negative

end CompressionStage

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

noncomputable def firstStage : CompressionStage f where
  Old := A
  Components := Task
  oldOrder := P
  batch := f.initial.batch
  original := (identityIso P).toMeetEmbedding
  inputs := f.initialInputs
  source_original _ := rfl
  top := f.greatest
  symmetry := f.initialSymmetry
  perm_eq _ _ := rfl
  representatives _ _ := rfl
  action_one := f.initialIso_one
  action_mul := f.initialIso_mul
  action_original := f.initialIso_old
  agreement := f.initial_agreement
  negative := f.initial_negative

noncomputable def stages : Nat → CompressionStage f
  | 0 => f.firstStage
  | n + 1 => (stages n).next

theorem stages_agreement (n : Nat) (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (x : (f.stages n).Old ⊕ (f.stages n).batch.Fresh)
    (below : (f.stages n).batch.extension.le x (.inl ((f.stages n).original.toFun v))) :
    ((f.stages n).symmetry g).current.toFun x =
      ((f.stages n).symmetry h).current.toFun x :=
  (f.stages n).agreement g h v agree x below

end TaskSystem
end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps.TaskSystem

open Attachment

universe u

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

def Point (n : Nat) : Type u := (f.stages n).Old

noncomputable def order (n : Nat) : MeetOrder (f.Point n) := (f.stages n).oldOrder

noncomputable def origin (n : Nat) : MeetEmbedding P (f.order n) := (f.stages n).original

noncomputable def step (n : Nat) : MeetEmbedding (f.order n) (f.order (n + 1)) :=
  (f.stages n).batch.oldEmbedding

noncomputable def compression (n : Nat) (i : Task) : MeetEmbedding (f.order n) (f.order (n + 1)) :=
  (f.stages n).inputs.previous i

noncomputable def stageAction : (n : Nat) → G → MeetIso (f.order n) (f.order n)
  | 0, g => f.action g
  | n + 1, g => ((f.stages n).symmetry g).current

theorem origins_coherent (n : Nat) (x : A) :
    (f.step n).toFun ((f.origin n).toFun x) = (f.origin (n + 1)).toFun x := rfl

theorem maps_coherent (n : Nat) (i : Task) (x : f.Point n) :
    (f.step (n + 1)).toFun ((f.compression n i).toFun x) =
      (f.compression (n + 1) i).toFun ((f.step n).toFun x) := rfl

theorem actions_coherent (n : Nat) (g : G) (x : f.Point n) :
    (f.step n).toFun ((f.stageAction n g).toFun x) =
      (f.stageAction (n + 1) g).toFun ((f.step n).toFun x) := by
  cases n <;> rfl

theorem stage_bottom (n : Nat) (zero : A) (bottom : ∀ x, P.le zero x) :
    ∀ x : f.Point n, (f.order n).le ((f.origin n).toFun zero) x := by
  induction n with
  | zero => exact bottom
  | succ n ih => exact (f.stages n).batch.least_preserved ((f.origin n).toFun zero) ih

theorem stageAction_one (n : Nat) (x : f.Point n) :
    (f.stageAction n f.group.one).toFun x = x := by
  cases n with
  | zero => exact f.action_one x
  | succ n => exact (f.stages n).action_one x

theorem stageAction_mul (n : Nat) (g h : G) (x : f.Point n) :
    (f.stageAction n (f.group.mul g h)).toFun x =
      (f.stageAction n g).toFun ((f.stageAction n h).toFun x) := by
  cases n with
  | zero => exact f.action_mul g h x
  | succ n => exact (f.stages n).action_mul g h x

theorem stageAction_original (n : Nat) (g : G) (x : A) :
    (f.stageAction n g).toFun ((f.origin n).toFun x) =
      (f.origin n).toFun ((f.action g).toFun x) := by
  cases n with
  | zero => rfl
  | succ n => exact (f.stages n).action_original g x

theorem stage_equivariant (n : Nat) (g : G) (i : Task) (x : f.Point n) :
    (f.stageAction (n + 1) g).toFun ((f.compression n i).toFun x) =
      (f.compression n (f.perm g i)).toFun x := by
  have h := ((f.stages n).symmetry g).intertwine i x
  rw [(f.stages n).perm_eq] at h
  exact h

theorem stage_agreement (n : Nat) (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (x : f.Point n) (below : (f.order n).le x ((f.origin n).toFun v)) :
    (f.stageAction n g).toFun x = (f.stageAction n h).toFun x := by
  cases n with
  | zero => exact agree x below
  | succ n => exact (f.stages n).agreement g h v agree x below

theorem stage_base_agreement (n : Nat) (i : Task) (x : f.Point n)
    (below : (f.order n).le x ((f.origin n).toFun (f.datum i).source)) :
    (f.compression n i).toFun x =
      (f.step n).toFun ((f.stageAction n (f.representative i)).toFun x) := by
  have hx : (f.stages n).oldOrder.le x ((f.stages n).inputs.source i) := by
    rw [(f.stages n).source_original]
    exact below
  exact ((f.stages n).inputs.agree i x hx).trans
    (((f.stages n).representatives i (.inl x)).symm.trans
      (f.actions_coherent n (f.representative i) x).symm)

theorem maps_base (n : Nat) (i : Task) :
    (f.compression n i).toFun ((f.origin n).toFun (f.datum i).source) =
      (f.origin (n + 1)).toFun (f.datum i).target := by
  rw [f.stage_base_agreement n i _ ((f.order n).refl _), f.stageAction_original,
    f.representative_target, f.origins_coherent]

noncomputable def cap (n : Nat) (i : Task) : f.Point (n + 1) :=
  (f.compression n i).toFun ((f.origin n).toFun f.top)

theorem caps_coherent (n : Nat) (i : Task) :
    (f.step (n + 1)).toFun (f.cap n i) = f.cap (n + 1) i :=
  f.maps_coherent n i ((f.origin n).toFun f.top)

theorem range_below_cap (n : Nat) (i : Task) (x : f.Point n) :
    (f.order (n + 1)).le ((f.compression n i).toFun x) (f.cap n i) :=
  ((f.compression n i).le_iff _ _).mpr ((f.stages n).top x)

theorem cap_separation (n : Nat) (i j : Task) (different : i ≠ j) :
    (f.order (n + 1)).le (f.cap n i) ((f.origin (n + 1)).toFun (f.datum j).target) ∨
    (f.order (n + 1)).le (f.cap n j) ((f.origin (n + 1)).toFun (f.datum i).target) ∨
    (f.order (n + 1)).meet (f.cap n i) (f.cap n j) =
      (f.order (n + 1)).meet ((f.origin (n + 1)).toFun (f.datum i).target)
        ((f.origin (n + 1)).toFun (f.datum j).target) := by
  induction n with
  | zero =>
    have h := f.initial.copy_cap_separation f.top f.greatest f.source_proper i j different
    have bi : f.initial.batch.base i = (f.datum i).target := f.representative_target i
    have bj : f.initial.batch.base j = (f.datum j).target := f.representative_target j
    rw [bi, bj] at h
    exact h
  | succ n ih =>
    rcases ih with h | h | h
    · have hn := ((f.step (n + 1)).le_iff _ _).mpr h
      rw [f.caps_coherent, f.origins_coherent] at hn
      exact Or.inl hn
    · have hn := ((f.step (n + 1)).le_iff _ _).mpr h
      rw [f.caps_coherent, f.origins_coherent] at hn
      exact Or.inr (Or.inl hn)
    · have hn := congrArg (f.step (n + 1)).toFun h
      rw [(f.step (n + 1)).map_meet, (f.step (n + 1)).map_meet,
        f.caps_coherent, f.caps_coherent, f.origins_coherent, f.origins_coherent] at hn
      exact Or.inr (Or.inr hn)

theorem original_below_cap (n : Nat) (i : Task) (v : A) :
    (f.order (n + 1)).le ((f.origin (n + 1)).toFun v) (f.cap n i) ↔ P.le v (f.datum i).target := by
  induction n with
  | zero =>
    change f.initial.batch.extension.le (.inl v) (f.initial.batch.represent i f.top) ↔ _
    rw [f.initial.batch.represent_new i f.top (f.source_proper i)]
    change P.le v (f.initial.batch.shadow ⟨i, ⟨f.top, f.source_proper i⟩⟩) ↔ _
    have hs := f.initial.batch.cap_shadow i f.top f.greatest (f.source_proper i)
    change f.initial.batch.shadow ⟨i, ⟨f.top, f.source_proper i⟩⟩ = _ at hs
    rw [hs]
    have hb : f.initial.batch.base i = (f.datum i).target := f.representative_target i
    rw [hb]
  | succ n ih =>
    rw [← f.caps_coherent n i, ← f.origins_coherent (n + 1) v]
    exact ((f.step (n + 1)).le_iff _ _).trans ih

theorem cap_strict (n : Nat) (i : Task) :
    (f.order (n + 1)).le ((f.origin (n + 1)).toFun (f.datum i).target) (f.cap n i) ∧
    ¬ (f.order (n + 1)).le (f.cap n i) ((f.origin (n + 1)).toFun (f.datum i).target) := by
  constructor
  · exact (f.original_below_cap n i _).mpr (P.refl _)
  · intro h
    rw [← f.maps_base n i] at h
    have lower := ((f.compression n i).le_iff _ _).mp h
    exact f.source_proper i (((f.origin n).le_iff _ _).mp lower)

theorem separator_not_below_cap (n : Nat) (i : Task) :
    ¬ (f.order (n + 1)).le ((f.origin (n + 1)).toFun (f.datum i).separator) (f.cap n i) :=
  fun h => (f.geometry i).separator_not_le_base ((f.original_below_cap n i _).mp h)

theorem stage_fresh_accounting (n : Nat) (z : (f.stages n).batch.Fresh) :
    ∃ (i : Task) (y : f.Point n), (f.compression n i).toFun y = .inr z ∧
      (f.order (n + 1)).le (.inr z) (f.cap n i) ∧
      ¬ (f.order (n + 1)).le (.inr z) ((f.origin (n + 1)).toFun (f.datum i).target) := by
  cases n with
  | zero =>
    rcases z with ⟨i, y, hy⟩
    have image := f.initial.batch.represent_new i y hy
    refine ⟨i, y, image, ?_, ?_⟩
    · have lower := f.range_below_cap 0 i y
      change f.initial.batch.extension.le (f.initial.batch.represent i y) _ at lower
      rw [image] at lower
      exact lower
    · exact fun h => (f.geometry i).separator_not_le_base
        ((f.geometry i).separator_le_filter _ h)
  | succ n =>
    rcases (f.stages n).inputs.fresh_accounting ((f.stages n).original.toFun f.top)
      (f.stages n).top z with ⟨i, y, image, lower, outside⟩
    refine ⟨i, y, image, lower, ?_⟩
    rw [← f.maps_base (n + 1) i]
    change ¬ (f.stages n).inputs.nextBatch.extension.le (.inr z)
      (.inl (((f.stages n).inputs.previous i).toFun ((f.stages n).original.toFun (f.datum i).source)))
    rw [← (f.stages n).source_original]
    exact outside

end PartitionPilot.Compression.RecursiveMaps.TaskSystem

end

end OAI
