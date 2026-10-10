import OAI.SetTheory.PartitionPrinciple.Forcing.StructuralForcingStageWitnessStep

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
open scoped ZFSet
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})
variable (shape : Q ⊆ ZFSet.prod c.carrier (ZFSet.powerset J))

include shape in
theorem presentedRowAssignmentOrder_code : PartialOrderCode Q (rawRowAssignmentOrder Q c.conditionOrder) := by
  rw [rawRowAssignmentOrder_eq shape]
  exact rowAssignmentOrder_partialOrder shape c.conditionOrder_code

variable (laws : RelationActionLaws G J (fun g => rawActionSection (t.encode g) B J))
variable (preserves : ∀ g : G, ∀ r : R, ∀ A,
  ZFSet.pair (c.encode r) A ∈ Q →
  ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q)

noncomputable def presentedRowAssignmentAction :
    letI := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
    PosetAction G (SetMembers Q) := by
  let := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
  have code : PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (SetMembers.presentation Q).conditionOrder
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B) := by
    rw [(presentedRowAssignmentOrder_code c Q J shape).conditionOrder_eq]
    exact presentedRowAssignmentGraph_code a c t Q J B shape laws preserves
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

theorem presentedRowAssignmentAction_graph :
    letI := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
    (presentedRowAssignmentAction a c t Q J B shape laws preserves).actionGraph (SetMembers.presentation Q) t =
      rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B := by
  let := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
  unfold presentedRowAssignmentAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem presentedRowAssignmentAction_coordinates :
    letI := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
    ∀ g (p : SetMembers Q) r A, SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((presentedRowAssignmentAction a c t Q J B shape laws preserves).iso g p) =
        ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) := by
  let := (presentedRowAssignmentOrder_code c Q J shape).toPartialOrder
  intro g p r A equal
  let act := presentedRowAssignmentAction a c t Q J B shape laws preserves
  have edge := (act.triple_mem_actionGraph (SetMembers.presentation Q) t g p (act.iso g p)).2 rfl
  rw [presentedRowAssignmentAction_graph a c t Q J B shape laws preserves] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw (act.iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c shape (SetMembers.raw_mem (act.iso g p))
  rw [equal, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g r q A D).1 edge
  rw [target, row, data]

end PartitionPilot.Forcing

end

end OAI
