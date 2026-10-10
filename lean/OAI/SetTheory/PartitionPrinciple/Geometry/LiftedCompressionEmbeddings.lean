import OAI.SetTheory.PartitionPrinciple.Definability.RecursiveActionRealization

namespace OAI

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem liftGraph_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair i.val (d.coding.encode x))
      (h.nextEncode M next (h.toInputs.lift i x)) ∈ h.liftGraph M next := by
  classical
  cases x with
  | inl x =>
    rw [h.toInputs.lift_old, h.nextEncode_old]
    exact (h.liftGraph_old_iff M next (h.maps.value_entry i) x.property).2
      (h.toInputs_previous_entry i x)
  | inr q =>
    by_cases positive : d.templates.upper q.1 (h.toInputs.source i)
    · rw [h.toInputs.lift_new_inside i q positive, h.nextEncode_old]
      exact (h.liftGraph_positive_iff M next (h.source_entry i) (d.filter_entry q.1)
        (h.actor_entry i) (d.freshCode_mem q) positive).2
        (h.toInputs_representative_entry i (.inr q))
    · rw [h.toInputs.lift_new_outside i q positive, h.nextEncode_fresh]
      exact (h.liftGraph_negative_iff M next (h.source_entry i) (d.filter_entry q.1)
        (d.freshCode_mem q) positive).2 rfl

theorem liftGraph_entry_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val (d.coding.encode x)) y ∈ h.liftGraph M next ↔
      y = h.nextEncode M next (h.toInputs.lift i x) := by
  constructor
  · intro entry
    exact (show FunctionGraphOn (ZFSet.prod I d.batchCarrier) (h.liftGraph M next) from
      ⟨next.batchCarrier, h.liftGraph_function M next⟩).unique entry (h.liftGraph_entry M next i x)
  · intro equal
    exact equal.symm ▸ h.liftGraph_entry M next i x

theorem liftSection_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (d.coding.encode x) (h.nextEncode M next (h.toInputs.lift i x)) ∈
      h.liftSection M next i.val :=
  (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    ⟨d.coding.encode_mem x, h.nextEncode_mem M next _, h.liftGraph_entry M next i x⟩

theorem liftSection_entry_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) (y : ZFSet.{u}) :
    ZFSet.pair (d.coding.encode x) y ∈ h.liftSection M next i.val ↔
      y = h.nextEncode M next (h.toInputs.lift i x) := by
  constructor
  · intro entry
    exact (h.liftGraph_entry_iff M next i x y).1
      ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 entry).2.2
  · intro equal
    exact equal.symm ▸ h.liftSection_entry M next i x

theorem liftSection_order_iff (i : {i : ZFSet.{u} // i ∈ I})
    {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ h.liftSection M next i.val)
    (second : ZFSet.pair y y' ∈ h.liftSection M next i.val) :
    ZFSet.pair x' y' ∈ next.batchOrder ↔ ZFSet.pair x y ∈ d.batchOrder := by
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
  have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
  obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
  rw [(h.liftSection_entry_iff M next i a x').1 first,
    (h.liftSection_entry_iff M next i b y').1 second, h.next_le_encode]
  exact ((h.toInputs.liftedEmbedding i).le_iff a b).trans (d.coding.le_encode a b).symm

theorem liftSection_injection (i : {i : ZFSet.{u} // i ∈ I}) :
    InjectionCode d.batchCarrier next.batchCarrier (h.liftSection M next i.val) where
  function := h.liftSection_function M next i.property
  injective := by
    intro x y z first second
    have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
    have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
    obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
    obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
    have equal := ((h.liftSection_entry_iff M next i a z).1 first).symm.trans
      ((h.liftSection_entry_iff M next i b z).1 second)
    exact congrArg d.coding.encode (h.toInputs.lift_injective i
      (h.nextEncode_injective M next equal))

theorem liftSection_map_meet (i : {i : ZFSet.{u} // i ∈ I})
    {x y z x' y' z' : ZFSet.{u}}
    (meet : ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph)
    (first : ZFSet.pair x x' ∈ h.liftSection M next i.val)
    (second : ZFSet.pair y y' ∈ h.liftSection M next i.val)
    (third : ZFSet.pair z z' ∈ h.liftSection M next i.val) :
    ZFSet.pair (ZFSet.pair x' y') z' ∈ next.batchMeetGraph := by
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
  have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
  obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
  have same : z = d.coding.encode (d.templates.extension.meet a b) :=
    (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
      ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique meet (d.coding.encoded_meet_entry a b)
  subst z
  rw [(h.liftSection_entry_iff M next i a x').1 first,
    (h.liftSection_entry_iff M next i b y').1 second,
    (h.liftSection_entry_iff M next i (d.templates.extension.meet a b) z').1 third]
  have preserved := (h.toInputs.liftedEmbedding i).map_meet a b
  change h.toInputs.lift i (d.templates.extension.meet a b) =
    h.toInputs.nextBatch.extension.meet (h.toInputs.lift i a) (h.toInputs.lift i b) at preserved
  rw [preserved]
  exact h.next_meet_entry M next (h.toInputs.lift i a) (h.toInputs.lift i b)

theorem liftSection_embedding (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbeddingCode d.batchCarrier next.batchCarrier d.batchOrder next.batchOrder
      d.batchMeetGraph next.batchMeetGraph (h.liftSection M next i.val) where
  injection := h.liftSection_injection M next i
  monotone := fun _ _ _ _ lower first second =>
    (h.liftSection_order_iff M next i first second).2 lower
  map_meet := fun _ _ _ _ _ _ meet first second third =>
    h.liftSection_map_meet M next i meet first second third

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
