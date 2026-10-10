import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveActions

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundEligibleBatchAction (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
  taggedActionGraph G P N A (M.groundEligibleFreshAction P G r μ A Labels)

theorem groundEligibleFreshAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleFreshAction P G r μ A Labels ∈ M.sets := by
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs (fields 0).1
  exact M.indexedTaskActionGraph_mem pairing unions powers separation hG hI hP hN
    (M.groundTaskTransport_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)

theorem groundEligibleBatchAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleBatchAction P G r μ A Labels ∈ M.sets := by
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs (fields 0).1
  exact M.taggedActionGraph_mem pairing unions powers separation hG hP hN hA
    (M.groundEligibleFreshAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)

theorem groundEligibleBatchCovariance
    {P G r μ A Labels m e : ZFSet.{u}} (action : PosetActionCode G P m e r A) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels)
    CodedAttachmentCovariance G P N A (M.groundEligibleFreshAction P G r μ A Labels)
      (batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r))
      (batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels))
      (batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  let T := M.groundTaskTransport P G r μ A Labels
  refine ⟨?_, ?_, ?_⟩
  · intro g hg q _ t _ q' _ t' _ first second inside
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, firstTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    obtain ⟨_, _, _, j, _, j', _, y, _, rfl, rfl, secondTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g t t').1 second
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 firstTask).2.2.2
    have tj := ((triple_mem_taskTransportGraph G I P R U Labels A g j j').1 secondTask).2.2.2
    exact ti.inside_covariant action hg tj hi' inside
  · intro g _ q _ q' _ p _ p' _ first acted shadow
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, task⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 task).2.2.2
    exact ti.shadow_covariant action hi' shadow acted
  · intro g _ q _ q' _ p _ p' _ first acted upper
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, task⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 task).2.2.2
    exact ti.upper_covariant action hi' upper acted

theorem groundEligibleBatchAction_code
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    PosetActionCode G d.batchCarrier m e d.batchOrder (M.groundEligibleBatchAction P G r μ A Labels) :=
  action.tagged_attachment
    (M.groundEligibleFreshAction_setAction pairing unions powers separation hP hG hA group action meet)
    (M.groundEligibleBatchCovariance action)

theorem groundEligibleBatchAction_old_iff
    {P G r μ A Labels g x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A :=
  taggedActionGraph_old_iff hx

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchAction_representation
    {P G r μ A Labels m inv e δ i j q x y : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let representation := batchAttachmentTemplateGraph I P
      (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair (ZFSet.pair i q) x ∈ representation →
    ZFSet.pair (ZFSet.pair j q) y ∈ representation →
    ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Qs := constantFamilyGraph I P
  let rs := constantFamilyGraph I r
  let As := literalTaskSourceGraph I P R U Labels
  let Es := literalTaskBaseGraph I P R U Labels
  let N := indexedAttachmentFresh I Qs rs As
  let T := M.groundTaskTransport P G r μ A Labels
  let B := M.groundEligibleFreshAction P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  dsimp only
  intro first second
  obtain ⟨hδ, hi, hj, transport⟩ :=
    (triple_mem_taskTransportGraph G I P R U Labels A δ i j).1 task
  let ii : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let jj : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
  obtain ⟨domain, _, branch⟩ :=
    (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es i q x).1 first
  obtain ⟨_, Q, fieldQ, hqQ⟩ := (pair_mem_indexedAttachmentDomain I Qs i q).1 domain
  have equalQ := ((pair_mem_constantFamilyGraph I P i Q).1 fieldQ).2
  have hq : q ∈ P := equalQ ▸ hqQ
  have newDomain : ZFSet.pair j q ∈ indexedAttachmentDomain I Qs :=
    (pair_mem_indexedAttachmentDomain I Qs j q).2
      ⟨hj, P, (pair_mem_constantFamilyGraph I P j P).2 ⟨hj, rfl⟩, hq⟩
  rcases branch with ⟨base, field, image⟩ | ⟨fresh, equal⟩
  · have image' : ZFSet.pair q x ∈ d.embed ii :=
      d.embeddings.unique field (d.embed_entry ii) ▸ image
    have hx := (ZFSet.pair_mem_prod.1 ((d.fiber ii).base_function.1 image')).2
    obtain ⟨v, acted, _⟩ := action.function.2 (ZFSet.pair δ x)
      (ZFSet.pair_mem_prod.2 ⟨hδ, hx⟩)
    have hv := (action.toSetAction.entry_shape acted).2.2
    have baseEq := transport.base_eq field (d.embed_entry jj)
    have newImage : ZFSet.pair q v ∈ d.embed jj := by
      rw [baseEq]
      exact (pair_mem_actionPostcompose P A δ base q v).2 ⟨hq, hv, x, hx, image, acted⟩
    have newEntry : ZFSet.pair (ZFSet.pair j q) v ∈
        batchAttachmentTemplateGraph I P Qs rs As Es :=
      (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es j q v).2
        ⟨newDomain, old_mem_taggedExtension hv, Or.inl ⟨d.embed jj, d.embed_entry jj, newImage⟩⟩
    have same : v = y := d.batch_template_unique jj newEntry second
    apply (triple_mem_taggedActionGraph G P N A B δ x y).2
    exact Or.inl (same ▸ acted)
  · have newFresh : ZFSet.pair j q ∈ N := (transport.fresh_iff hi hj).1 fresh
    have newEntry : ZFSet.pair (ZFSet.pair j q) (ZFSet.pair P (ZFSet.pair j q)) ∈
        batchAttachmentTemplateGraph I P Qs rs As Es :=
      (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es j q _).2
        ⟨newDomain, pair_mem_taggedExtension.2 newFresh, Or.inr ⟨newFresh, rfl⟩⟩
    have same : ZFSet.pair P (ZFSet.pair j q) = y := d.batch_template_unique jj newEntry second
    have moved : ZFSet.pair (ZFSet.pair δ (ZFSet.pair i q)) (ZFSet.pair j q) ∈ B :=
      (triple_mem_indexedTaskActionGraph G I P N T δ (ZFSet.pair i q) (ZFSet.pair j q)).2
        ⟨hδ, fresh, newFresh, i, hi, j, hj, q, hq, rfl, rfl, task⟩
    exact (triple_mem_taggedActionGraph G P N A B δ x y).2
      (Or.inr ⟨hδ, ZFSet.pair i q, fresh, ZFSet.pair j q, newFresh, equal, same.symm, moved⟩)

theorem groundEligibleBatchAction_equivariant
    {P G r μ A Labels m inv e δ i j q x y : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let copies := batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair q x ∈ copies i → ZFSet.pair q y ∈ copies j →
    ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  intro first second
  exact M.groundEligibleBatchAction_representation group action meet task
    ((pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).1 first)
    ((pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).1 second)

end PartitionPilot.Forcing.TransitiveGround

end OAI
