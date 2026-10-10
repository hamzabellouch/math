import OAI.SetTheory.PartitionPrinciple.Forcing.EligibleBatchEquivariance

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

universe u

theorem groundEligibleFreshAction_positive_agreement (M : TransitiveGround.{u})
    {P G r μ A Labels m inv e g h v q q' q'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v)
    (first : ZFSet.pair (ZFSet.pair g q) q' ∈ M.groundEligibleFreshAction P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h q) q'' ∈ M.groundEligibleFreshAction P G r μ A Labels)
    (upper : ZFSet.pair q v ∈ batchAttachmentUpperGraph
      (M.groundEligibleTasks P G r μ A Labels) P
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) P)
      (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)) : q' = q'' := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  let T := M.groundTaskTransport P G r μ A Labels
  obtain ⟨_, _, _, i, hi, i', _, x, _, source, target, firstTask⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
  obtain ⟨_, _, _, j, _, j', _, y, _, source', target', secondTask⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T h q q'').1 second
  have indices : i = j := (ZFSet.pair_inj.1 (source.symm.trans source')).1
  have points : x = y := (ZFSet.pair_inj.1 (source.symm.trans source')).2
  subst j y
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  subst i
  rw [source] at upper
  have positive := ((literalTask_upper_iff ha hc hb hs hF hl).1 upper).2.2.2
  have same := M.groundTaskTransport_positive_agreement group action meet agree positive firstTask secondTask
  exact target.trans ((congrArg (fun task => ZFSet.pair task x) same).trans target'.symm)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

theorem codedAttachmentOrder_below_old
    {P N r inside shadow upper x v : ZFSet.{u}} (hv : v ∈ P) :
    ZFSet.pair x v ∈ codedAttachmentOrder P N r inside shadow upper ↔
      (x ∈ P ∧ ZFSet.pair x v ∈ r) ∨
        ∃ q ∈ N, x = ZFSet.pair P q ∧ ZFSet.pair q v ∈ upper := by
  rw [pair_mem_codedAttachmentOrder]
  constructor
  · rintro ⟨_, _, old | oldFresh | freshOld | freshFresh⟩
    · exact Or.inl ⟨old.1, old.2.2⟩
    · obtain ⟨_, q, _, _, _, equal, _⟩ := oldFresh
      exact False.elim (pair_tag_not_mem P q (equal ▸ hv))
    · exact Or.inr freshOld.2
    · obtain ⟨_, _, t, _, _, equal, _⟩ := freshFresh
      exact False.elim (pair_tag_not_mem P t (equal ▸ hv))
  · rintro (⟨hx, lower⟩ | ⟨q, hq, rfl, upperEntry⟩)
    · exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension hv, Or.inl ⟨hx, hv, lower⟩⟩
    · exact ⟨pair_mem_taggedExtension.2 hq, old_mem_taggedExtension hv,
        Or.inr (Or.inr (Or.inl ⟨hv, q, hq, rfl, upperEntry⟩))⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchAction_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e g h v : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G) (hv : v ∈ P)
    (agree : ActionAgreementBelow P r A g h v) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ActionAgreementBelow d.batchCarrier d.batchOrder (M.groundEligibleBatchAction P G r μ A Labels) g h v := by
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let B := M.groundEligibleBatchAction P G r μ A Labels
  have full := M.groundEligibleBatchAction_code (Labels := Labels)
    pairing unions powers separation hP hG hA group action meet
  have fresh := M.groundEligibleFreshAction_setAction (Labels := Labels)
    pairing unions powers separation hP hG hA group action meet
  have outputs {x y z : ZFSet.{u}} (lower : ZFSet.pair x v ∈ d.batchOrder)
      (first : ZFSet.pair (ZFSet.pair g x) y ∈ B)
      (second : ZFSet.pair (ZFSet.pair h x) z ∈ B) : y = z := by
    rcases (codedAttachmentOrder_below_old hv).1 lower with ⟨hx, below⟩ | ⟨q, _, rfl, upper⟩
    · exact agree.entry_eq action hh hx below
        ((M.groundEligibleBatchAction_old_iff hx).1 first)
        ((M.groundEligibleBatchAction_old_iff hx).1 second)
    · obtain ⟨q', _, rfl, firstFresh⟩ :=
        (taggedActionGraph_fresh_iff action.toSetAction fresh).1 first
      obtain ⟨q'', _, rfl, secondFresh⟩ :=
        (taggedActionGraph_fresh_iff action.toSetAction fresh).1 second
      exact congrArg (ZFSet.pair P)
        (M.groundEligibleFreshAction_positive_agreement group action meet agree firstFresh secondFresh upper)
  change ActionAgreementBelow d.batchCarrier d.batchOrder B g h v
  intro x hx y _ lower
  constructor
  · intro first
    obtain ⟨z, second, _⟩ := full.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
    exact (outputs lower first second).symm ▸ second
  · intro second
    obtain ⟨z, first, _⟩ := full.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    exact outputs lower first second ▸ first

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
