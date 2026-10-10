import OAI.SetTheory.PartitionPrinciple.Geometry.InitialRepresentativeAgreement

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem TaskRepresentative.source_mem
    {P r A R U Labels I i g a : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels i g)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels) : a ∈ P := by
  obtain ⟨a', ha, c, hc, base, hb, s, hs, F, hF, label, hl, equal, _⟩ := represented
  have aEq : a = a' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (equal ▸ source)).2
  exact aEq.symm ▸ ha

theorem TaskTransportCode.representative_product_agreement
    {P R U Labels A δ i j G m one r g h k I a : ZFSet.{u}}
    (transport : TaskTransportCode P R U Labels A δ i j)
    (action : PosetActionCode G P m one r A)
    (hδ : δ ∈ G) (hg : g ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair δ g) k ∈ m)
    (first : TaskRepresentative P r A R U Labels i g)
    (second : TaskRepresentative P r A R U Labels j h)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels) :
    ActionAgreementBelow P r A k h a := by
  obtain ⟨a', ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', _, base', _, s', _, F', _, old, new, target, _, baseEq, _⟩ := transport
  have aEq : a = a' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (old ▸ source)).2
  have oldRestriction := (old ▸ first).restriction
  have newRestriction := (new ▸ second).restriction
  have composed := oldRestriction.transport action hg hδ hk product target
  rw [baseEq] at newRestriction
  intro x hx y _ lower
  exact (composed.base_action_iff action hx (aEq ▸ lower)).symm.trans
    (newRestriction.base_action_iff action hx (aEq ▸ lower))

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundTaskRepresentatives_product_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one Reps δ i j g h k a : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (reps : ZFSet.IsFunc (M.groundEligibleTasks P G r μ A Labels) G Reps)
    (represents : ∀ i g, ZFSet.pair i g ∈ Reps →
      TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels i g)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (first : ZFSet.pair i g ∈ Reps) (second : ZFSet.pair j h ∈ Reps)
    (product : ZFSet.pair (ZFSet.pair δ g) k ∈ m) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ActionAgreementBelow d.batchCarrier d.batchOrder
      (M.groundEligibleBatchAction P G r μ A Labels) k h a := by
  have transported := (triple_mem_taskTransportGraph G _ P _ _ Labels A δ i j).1 task
  have hg := (ZFSet.pair_mem_prod.1 (reps.1 first)).2
  have hh := (ZFSet.pair_mem_prod.1 (reps.1 second)).2
  have hk := (ZFSet.pair_mem_prod.1 (group.mul_function.1 product)).2
  have old := transported.2.2.2.representative_product_agreement action transported.1 hg hk
    product (represents i g first) (represents j h second) source
  exact M.groundEligibleBatchAction_agreement pairing unions powers separation hP hG hA
    group action meet hk hh ((represents i g first).source_mem source) old

theorem groundTaskRepresentatives_composed_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one Reps δ i j g h a x y z : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (reps : ZFSet.IsFunc (M.groundEligibleTasks P G r μ A Labels) G Reps)
    (represents : ∀ i g, ZFSet.pair i g ∈ Reps →
      TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels i g)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (first : ZFSet.pair i g ∈ Reps) (second : ZFSet.pair j h ∈ Reps)
    (hx : x ∈ (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchCarrier)
    (lower : ZFSet.pair x a ∈
      (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchOrder)
    (firstAction : ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels)
    (secondAction : ZFSet.pair (ZFSet.pair h x) z ∈ M.groundEligibleBatchAction P G r μ A Labels) :
    ZFSet.pair (ZFSet.pair δ y) z ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  have transported := (triple_mem_taskTransportGraph G _ P _ _ Labels A δ i j).1 task
  have hg := (ZFSet.pair_mem_prod.1 (reps.1 first)).2
  have hh := (ZFSet.pair_mem_prod.1 (reps.1 second)).2
  obtain ⟨k, product, _⟩ := group.mul_function.2 (ZFSet.pair δ g)
    (ZFSet.pair_mem_prod.2 ⟨transported.1, hg⟩)
  have hk := (ZFSet.pair_mem_prod.1 (group.mul_function.1 product)).2
  have agree := M.groundTaskRepresentatives_product_agreement pairing unions powers separation
    hP hG hA group action meet reps represents task source first second product
  have full := M.groundEligibleBatchAction_code (Labels := Labels)
    pairing unions powers separation hP hG hA group action meet
  have hy := (ZFSet.pair_mem_prod.1 (full.function.1 firstAction)).2
  obtain ⟨w, acted, _⟩ := full.function.2 (ZFSet.pair δ y)
    (ZFSet.pair_mem_prod.2 ⟨transported.1, hy⟩)
  have hw := (ZFSet.pair_mem_prod.1 (full.function.1 acted)).2
  have composed := full.mul δ transported.1 g hg k hk x hx y hy w hw product firstAction acted
  have equal := agree.entry_eq full hh hx lower composed secondAction
  exact equal ▸ acted

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
