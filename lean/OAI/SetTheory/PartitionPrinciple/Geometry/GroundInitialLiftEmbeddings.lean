import OAI.SetTheory.PartitionPrinciple.Transfinite.InitialRecursiveTaskLaws
import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveNextMapInputs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialLiftEmbeddings
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) As (literalTaskBaseGraph I P R U Labels)
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    ∃ Reps ∈ M.sets, ∃ h : CodedRecursiveMapInputs d I Maps As Reps G m inv one B,
      ∃ next : h.NextInputs M,
        next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
        MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
        h.liftGraph M next ∈ M.sets ∧
        ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
        h.groundLiftFamily M next ∈ M.sets ∧ FunctionGraphOn I (h.groundLiftFamily M next) ∧
        (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
        ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
          MeetEmbeddingCode d.batchCarrier next.batchCarrier d.batchOrder next.batchOrder
            d.batchMeetGraph next.batchMeetGraph f ∧
          ∀ a g x y, ZFSet.pair i a ∈ As → ZFSet.pair i g ∈ Reps →
            x ∈ d.batchCarrier → ZFSet.pair x a ∈ d.batchOrder →
              (ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ B) := by
  obtain ⟨hI, hSources, hMaps, hB, Reps, hReps, inputs⟩ := M.exists_groundInitialRecursiveInputs
    pairing unions powers separation choice hP hG hr hμ hA hLabels group action meet
  obtain ⟨_, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  exact ⟨Reps, hReps, inputs, inputs.exists_groundLiftEmbeddings M pairing unions powers separation
    hI hI hP hr hQs hrs hμs (fields 0).1 (fields 2).1 (fields 4).1 (fields 3).1
    hMaps hSources hReps hG hB⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
