import OAI.SetTheory.PartitionPrinciple.Definability.RepresentativeProductAgreement
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInvariantSuccessors

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialRecursiveSuccessor
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
    let T := M.groundTaskTransport P G r μ A Labels
    ∃ Reps ∈ M.sets, ∃ h : CodedRecursiveMapInputs d I Maps As Reps G m inv one B,
      ∃ next : h.NextInputs M,
        next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
        MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
        h.nextActionGraph T ∈ M.sets ∧
        PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T) ∧
        h.liftGraph M next ∈ M.sets ∧
        ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
        h.groundLiftFamily M next ∈ M.sets ∧
        (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
        ∃ nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) As Reps
          G m inv one (h.nextActionGraph T), CodedRecursiveTaskAction nextInputs T := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let As := literalTaskSourceGraph I P R U Labels
  let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
    (constantFamilyGraph I r) As (literalTaskBaseGraph I P R U Labels)
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let B := M.groundEligibleBatchAction P G r μ A Labels
  let T := M.groundTaskTransport P G r μ A Labels
  obtain ⟨hI, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, valid, hB, currentAction,
    Reps, hReps, reps, represents, agreement⟩ :=
    M.exists_groundInitialRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet
  let h : CodedRecursiveMapInputs d I Maps As Reps G m inv one B :=
    ⟨maps, (fields 0).2, reps, group, currentAction, valid, agreement⟩
  have s := M.groundInitialTaskAction pairing unions powers separation hP hG hr hμ hA hLabels
    group action meet Reps h
  have compatible : RecursiveRepresentativeCompatibility h T := by
    intro δ i j a g g' x y z transport source first second hx below left right
    exact M.groundTaskRepresentatives_composed_entry pairing unions powers separation
      hP hG hA group action meet reps represents transport source first second hx below left right
  exact ⟨Reps, hReps, h, s.exists_groundSuccessor M pairing unions powers separation
    compatible hI hI hP hr hQs hrs hμs (fields 0).1 (fields 2).1 (fields 4).1 (fields 3).1
    hMaps (fields 0).1 hReps hG hB
    (M.groundTaskTransport_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
