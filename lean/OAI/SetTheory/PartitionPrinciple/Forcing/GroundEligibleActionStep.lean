import OAI.SetTheory.PartitionPrinciple.Geometry.EligibleBatchAgreement

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchAction_order_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e g x y x' y' : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G)
    (first : ZFSet.pair (ZFSet.pair g x) x' ∈ M.groundEligibleBatchAction P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair g y) y' ∈ M.groundEligibleBatchAction P G r μ A Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair x' y' ∈ d.batchOrder ↔ ZFSet.pair x y ∈ d.batchOrder :=
  (M.groundEligibleBatchAction_code pairing unions powers separation hP hG hA group action meet).raw_order_iff
    group (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batch_meetOrder.order hg first second

theorem groundEligibleBatchAction_map_meet
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e g x y z x' y' z' : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G)
    (first : ZFSet.pair (ZFSet.pair g x) x' ∈ M.groundEligibleBatchAction P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair g y) y' ∈ M.groundEligibleBatchAction P G r μ A Labels)
    (third : ZFSet.pair (ZFSet.pair g z) z' ∈ M.groundEligibleBatchAction P G r μ A Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph →
      ZFSet.pair (ZFSet.pair x' y') z' ∈ d.batchMeetGraph :=
  fun oldMeet => (M.groundEligibleBatchAction_code pairing unions powers separation hP hG hA group action meet).raw_map_meet
    group (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batch_meetOrder hg oldMeet first second third

theorem groundEligibleTaskActionStep
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧ B ∈ M.sets ∧
      MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph ∧
      PosetActionCode G d.batchCarrier m e d.batchOrder B ∧
      (∀ g h v, g ∈ G → h ∈ G → v ∈ P → ActionAgreementBelow P r A g h v →
        ActionAgreementBelow d.batchCarrier d.batchOrder B g h v) ∧
      (∀ g x y, x ∈ P →
        (ZFSet.pair (ZFSet.pair g x) y ∈ B ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A)) := by
  have batch := M.groundEligibleTaskAttachment pairing unions powers separation hP hG hr hμ hA hLabels
    group action meet
  exact ⟨batch.1, batch.2.1, batch.2.2.1,
    M.groundEligibleBatchAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet,
    (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batch_meetOrder,
    M.groundEligibleBatchAction_code pairing unions powers separation hP hG hA group action meet,
    fun _ _ _ hg hh hv agree => M.groundEligibleBatchAction_agreement
      pairing unions powers separation hP hG hA group action meet hg hh hv agree,
    fun _ _ _ hx => M.groundEligibleBatchAction_old_iff hx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
