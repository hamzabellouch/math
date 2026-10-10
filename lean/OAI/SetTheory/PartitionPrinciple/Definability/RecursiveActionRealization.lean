import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveActions

namespace OAI

section

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open Compression.RecursiveMaps
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_upper (label : h.toInputs.Labels)
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    next.templates.upper (h.nextIndex label) ⟨d.coding.encode x, d.coding.encode_mem x⟩ ↔
      h.toInputs.nextBatch.upper label x := by
  change d.coding.encode x ∈ next.filter (h.nextIndex label) ↔ _
  rw [h.next_filter M next, mem_pushFilterCode]
  constructor
  · rintro ⟨_, a, ha, z, _, entry, lower⟩
    let a' : {a : ZFSet.{u} // a ∈ D} := ⟨a, (d.fiber label.2.val).filter.subset ha⟩
    have equal := (show FunctionGraphOn D (h.maps.value label.1) from
      ⟨d.batchCarrier, (h.valid _ _ (h.maps.value_entry label.1)).injection.function⟩).unique
      entry (h.toInputs_previous_entry label.1 a')
    exact ⟨a', ha, (d.coding.le_encode _ x).1 (equal ▸ lower)⟩
  · rintro ⟨a, ha, lower⟩
    exact ⟨d.coding.encode_mem x, a.val, ha,
      d.coding.encode ((h.toInputs.previous label.1).toFun a), d.coding.encode_mem _,
      h.toInputs_previous_entry label.1 a, (d.coding.le_encode _ x).2 lower⟩

theorem nextFresh_shadow (q : h.toInputs.nextBatch.Fresh) :
    (next.templates.shadow (h.nextFresh M next q)).val =
      d.coding.encode (h.toInputs.nextBatch.shadow q) := by
  have oldEntry := (d.fiber q.1.2.val).shadow_entry ⟨(), q.2⟩
  obtain ⟨_, _, c, hc, meetEntry, baseEntry⟩ :=
    (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).1 oldEntry
  apply Eq.symm
  apply next.freshCode_shadow_value (h.nextFresh M next q)
  apply (next.batch_shadow_entry_iff (h.nextIndex q.1) q.2.val.val _).2
  rw [h.next_space M next, h.next_meet M next, h.next_embed M next, h.next_anchor M next]
  apply (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).2
  refine ⟨q.2.val.property, d.coding.encode_mem _, c, hc, meetEntry, ?_⟩
  apply (pair_mem_relationCompose _ _ _ _ _ _ _).2
  refine ⟨mem_familyPointBound_of_entry (d.space_entry q.1.2.val) hc,
    d.coding.encode_mem _, (d.templates.shadow ⟨q.1.2.val, q.2⟩).val,
    (d.templates.shadow ⟨q.1.2.val, q.2⟩).property, baseEntry, ?_⟩
  exact h.toInputs_previous_entry q.1.1 (d.templates.shadow ⟨q.1.2.val, q.2⟩)

noncomputable def nextNodes :
    ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh →
      {x : ZFSet.{u} // x ∈ d.batchCarrier} ⊕ next.templates.Fresh
  | .inl x => .inl ⟨d.coding.encode x, d.coding.encode_mem x⟩
  | .inr q => .inr (h.nextFresh M next q)

noncomputable def nextEncode
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.{u} := next.coding.encode (h.nextNodes M next x)

theorem nextEncode_old (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    h.nextEncode M next (.inl x) = d.coding.encode x := rfl

theorem nextEncode_fresh (q : h.toInputs.nextBatch.Fresh) :
    h.nextEncode M next (.inr q) = ZFSet.pair d.batchCarrier
      (ZFSet.pair (ZFSet.pair q.1.1.val q.1.2.val.val) q.2.val.val) := rfl

theorem nextEncode_mem
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    h.nextEncode M next x ∈ next.batchCarrier := next.coding.encode_mem _

theorem nextNodes_injective : Function.Injective (h.nextNodes M next) := by
  intro x y equal
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (d.coding.encode_injective
        (congrArg Subtype.val (Sum.inl.inj equal)))
    | inr y => cases equal
  | inr x =>
    cases y with
    | inl y => cases equal
    | inr y => exact congrArg Sum.inr (h.nextFresh_injective M next (Sum.inr.inj equal))

theorem nextNodes_surjective : Function.Surjective (h.nextNodes M next) := by
  intro x
  cases x with
  | inl x =>
    obtain ⟨y, equal⟩ := d.coding.encode_surjective x.val x.property
    exact ⟨.inl y, congrArg Sum.inl (Subtype.ext equal)⟩
  | inr q =>
    obtain ⟨p, equal⟩ := h.nextFresh_surjective M next q
    exact ⟨.inr p, congrArg Sum.inr equal⟩

theorem nextEncode_injective : Function.Injective (h.nextEncode M next) :=
  fun _ _ equal => h.nextNodes_injective M next (next.coding.encode_injective equal)

theorem nextEncode_surjective : ∀ z ∈ next.batchCarrier,
    ∃ x, h.nextEncode M next x = z := by
  intro z hz
  obtain ⟨y, equal⟩ := next.coding.encode_surjective z hz
  obtain ⟨x, rfl⟩ := h.nextNodes_surjective M next y
  exact ⟨x, equal⟩

theorem next_le_encode
    (x y : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (h.nextEncode M next x) (h.nextEncode M next y) ∈ next.batchOrder ↔
      h.toInputs.nextBatch.extension.le x y := by
  change ZFSet.pair (next.coding.encode (h.nextNodes M next x))
    (next.coding.encode (h.nextNodes M next y)) ∈ next.batchOrder ↔ _
  rw [next.coding.le_encode]
  cases x with
  | inl x =>
    cases y with
    | inl y => exact d.coding.le_encode x y
    | inr q =>
      change ZFSet.pair (d.coding.encode x) (next.templates.shadow (h.nextFresh M next q)).val ∈
        d.batchOrder ↔ d.templates.extension.le x (h.toInputs.nextBatch.shadow q)
      rw [h.nextFresh_shadow M next]
      exact d.coding.le_encode x _
  | inr q =>
    cases y with
    | inl y => exact h.next_upper M next q.1 y
    | inr t =>
      change (next.templates.Inside (h.nextFresh M next q) (h.nextFresh M next t) ∨
        next.templates.upper (h.nextIndex q.1) (next.templates.shadow (h.nextFresh M next t))) ↔
        (h.toInputs.nextBatch.Inside q t ∨
          h.toInputs.nextBatch.upper q.1 (h.toInputs.nextBatch.shadow t))
      apply or_congr (h.nextFresh_inside_iff M next q t)
      have equal : next.templates.shadow (h.nextFresh M next t) =
          ⟨d.coding.encode (h.toInputs.nextBatch.shadow t), d.coding.encode_mem _⟩ :=
        Subtype.ext (h.nextFresh_shadow M next t)
      rw [equal]
      exact h.next_upper M next q.1 _

theorem next_meet_entry
    (x y : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (ZFSet.pair (h.nextEncode M next x) (h.nextEncode M next y))
      (h.nextEncode M next (h.toInputs.nextBatch.extension.meet x y)) ∈ next.batchMeetGraph := by
  apply next.batch_meetOrder.pair_iff.2
  refine ⟨h.nextEncode_mem M next x, h.nextEncode_mem M next y, h.nextEncode_mem M next _,
    (h.next_le_encode M next _ x).2 (h.toInputs.nextBatch.extension.meet_le_left x y),
    (h.next_le_encode M next _ y).2 (h.toInputs.nextBatch.extension.meet_le_right x y), ?_⟩
  intro z hz zx zy
  obtain ⟨w, rfl⟩ := h.nextEncode_surjective M next z hz
  exact (h.next_le_encode M next _ _).2 (h.toInputs.nextBatch.extension.le_meet
    ((h.next_le_encode M next _ _).1 zx) ((h.next_le_encode M next _ _).1 zy))

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem nextAction_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (h.nextEncode M next x))
      (h.nextEncode M next ((s.toTaskSymmetry g).nextIso.toFun x)) ∈ h.nextActionGraph T := by
  cases x with
  | inl x =>
    rw [(s.toTaskSymmetry g).nextIso_old, h.nextEncode_old, h.nextEncode_old]
    exact (h.nextAction_old_iff (d.coding.encode_mem x)).2 (s.toTaskSymmetry_current_entry g x)
  | inr q =>
    rw [(s.toTaskSymmetry g).nextIso_fresh, h.nextEncode_fresh, h.nextEncode_fresh]
    exact h.nextAction_fresh_entry s.taskAction s.source
      (s.toTaskSymmetry_perm_entry g q.1.1) (next.freshCode_mem (h.nextFresh M next q))

theorem nextAction_entry_iff (g : {g : ZFSet.{u} // g ∈ G})
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh)
    (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g.val (h.nextEncode M next x)) y ∈ h.nextActionGraph T ↔
      y = h.nextEncode M next ((s.toTaskSymmetry g).nextIso.toFun x) := by
  constructor
  · intro entry
    exact (h.nextAction_setAction s.taskAction s.source M next).entry_unique entry
      (s.nextAction_entry M next g x)
  · intro equal
    exact equal.symm ▸ s.nextAction_entry M next g x

include s in
theorem nextAction_order_iff {g x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair g x) x' ∈ h.nextActionGraph T)
    (second : ZFSet.pair (ZFSet.pair g y) y' ∈ h.nextActionGraph T) :
    ZFSet.pair x' y' ∈ next.batchOrder ↔ ZFSet.pair x y ∈ next.batchOrder := by
  have sx := (h.nextAction_setAction s.taskAction s.source M next).entry_shape first
  have sy := (h.nextAction_setAction s.taskAction s.source M next).entry_shape second
  let actor : {g : ZFSet.{u} // g ∈ G} := ⟨g, sx.1⟩
  obtain ⟨a, rfl⟩ := h.nextEncode_surjective M next x sx.2.1
  obtain ⟨b, rfl⟩ := h.nextEncode_surjective M next y sy.2.1
  rw [(s.nextAction_entry_iff M next actor a x').1 first,
    (s.nextAction_entry_iff M next actor b y').1 second, h.next_le_encode, h.next_le_encode]
  exact (s.toTaskSymmetry actor).nextIso.le_iff a b

include s in
theorem nextAction_code :
    PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T) where
  function := (h.nextAction_setAction s.taskAction s.source M next).function
  one := (h.nextAction_setAction s.taskAction s.source M next).one
  mul := (h.nextAction_setAction s.taskAction s.source M next).mul
  monotone := fun _ _ _ _ _ _ _ _ _ _ first second lower =>
    (s.nextAction_order_iff M next first second).2 lower

include s in
theorem nextAction_map_meet {g x y z x' y' z' : ZFSet.{u}}
    (meet : ZFSet.pair (ZFSet.pair x y) z ∈ next.batchMeetGraph)
    (first : ZFSet.pair (ZFSet.pair g x) x' ∈ h.nextActionGraph T)
    (second : ZFSet.pair (ZFSet.pair g y) y' ∈ h.nextActionGraph T)
    (third : ZFSet.pair (ZFSet.pair g z) z' ∈ h.nextActionGraph T) :
    ZFSet.pair (ZFSet.pair x' y') z' ∈ next.batchMeetGraph :=
  (s.nextAction_code M next).raw_map_meet h.group next.batch_meetOrder
    ((h.nextAction_setAction s.taskAction s.source M next).entry_shape first).1
    meet first second third

end PartitionPilot.Forcing.CodedRecursiveTaskAction

end

end OAI
