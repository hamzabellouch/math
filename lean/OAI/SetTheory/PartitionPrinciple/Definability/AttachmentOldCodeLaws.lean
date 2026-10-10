import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchAttachment

namespace OAI

section

namespace PartitionPilot.Forcing.AttachmentBatchInputs
universe u
variable {P r μ J Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)

theorem old_order_iff {x y : ZFSet.{u}} (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair x y ∈ d.batchOrder ↔ ZFSet.pair x y ∈ r :=
  d.coding.le_encode (.inl ⟨x, hx⟩) (.inl ⟨y, hy⟩)

theorem old_meet_entry {x y z : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair x y) z ∈ μ) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph := by
  have shape := ZFSet.pair_mem_prod.1 (d.oldOrder.operation.1 entry)
  have inputs := ZFSet.pair_mem_prod.1 shape.1
  exact d.coding.old_embedding_code.map_meet x y z x y z entry
    ((pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨inputs.1, rfl⟩)
    ((pair_mem_attachmentOldEmbeddingGraph P y y).2 ⟨inputs.2, rfl⟩)
    ((pair_mem_attachmentOldEmbeddingGraph P z z).2 ⟨shape.2, rfl⟩)

theorem old_meet_iff {x y z : ZFSet.{u}} (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ μ := by
  constructor
  · intro entry
    obtain ⟨w, old, _⟩ := d.oldOrder.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have same : z = w :=
      (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
        ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique entry (d.old_meet_entry old)
    exact same.symm ▸ old
  · exact d.old_meet_entry

end PartitionPilot.Forcing.AttachmentBatchInputs

end

end OAI
