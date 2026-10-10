import OAI.SetTheory.PartitionPrinciple.Geometry.InitialRepresentativeAgreement

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialRecursiveInputs
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
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      As (literalTaskBaseGraph I P R U Labels)
    let B := M.groundEligibleBatchAction P G r μ A Labels
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    I ∈ M.sets ∧ As ∈ M.sets ∧ Maps ∈ M.sets ∧ B ∈ M.sets ∧
      ∃ representatives ∈ M.sets,
        CodedRecursiveMapInputs d I Maps As representatives G m inv one B := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, valid, hB, currentAction,
    representatives, ground, function, _, agreement⟩ :=
    M.exists_groundInitialRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet
  exact ⟨hI, (fields 0).1, hMaps, hB, representatives, ground,
    ⟨maps, (fields 0).2, function, group, currentAction, valid, agreement⟩⟩

theorem groundInitialMap_cap_base
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T i S a c : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
      ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
      ZFSet.IsFunc P d.batchCarrier S ∧
        ZFSet.pair T (eligibleTaskCap P T i) ∈ S ∧ ZFSet.pair a c ∈ S := by
  dsimp only
  intro mapEntry source target
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  obtain ⟨hi, mapEq⟩ := (entries i S).1 mapEntry
  rw [mapEq]
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
  have function : ZFSet.IsFunc P d.batchCarrier
      (batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
        (literalTaskBaseGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) i) := by
    simpa only [spaceEq] using d.batch_template_fiber_function j
  refine ⟨function, (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
    (M.groundEligibleTask_cap_entry group action meet hT top hi), ?_⟩
  obtain ⟨a', ha, c', hc, base, hb, s, hs, F, hF, label, hl, equal, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  have aEq : a = a' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (equal ▸ source)).2
  have cEq : c = c' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 1).1 (equal ▸ target)).2
  have baseEntry : ZFSet.pair i base ∈ literalTaskBaseGraph I P
      (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨equal ▸ hi, rfl⟩
  have baseEq : d.embed j = base := d.embeddings.unique (d.embed_entry j) baseEntry
  obtain ⟨g, _, represented⟩ := code.representative
  have entry : ZFSet.pair a' c' ∈ base :=
    (represented.entries a' ha c' hc).2 ⟨meet.order.refl a' ha, represented.target_entry⟩
  rw [aEq, cEq]
  exact (d.batch_template_old_agreement j (baseEq.symm ▸ entry)).1

theorem groundInitialMap_negative_cap
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T i S a c F K b v w : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
      ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
      ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels →
      ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S → v ∈ P → v ∉ F →
      ZFSet.pair (ZFSet.pair K v) w ∈ d.batchMeetGraph → ZFSet.pair w b ∈ d.batchOrder := by
  dsimp only
  intro mapEntry source target filter cap base hv negative entry
  obtain ⟨function, capEntry, baseEntry⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels group action meet hT top
    mapEntry source target
  obtain ⟨_, _, uniqueCap⟩ := function.2 T hT
  have capEq : K = eligibleTaskCap P T i :=
    (uniqueCap K cap).trans (uniqueCap _ capEntry).symm
  have sourceShape := (ZFSet.mem_sep.1 source).1
  have ha := (ZFSet.pair_mem_prod.1 sourceShape).2
  obtain ⟨_, _, uniqueBase⟩ := function.2 a ha
  have baseEq : b = c := (uniqueBase b base).trans (uniqueBase c baseEntry).symm
  have hi := (ZFSet.pair_mem_prod.1 sourceShape).1
  exact baseEq.symm ▸ (M.groundEligibleTask_negative_cap group action meet hT top hi
    target filter hv negative (capEq ▸ entry)).2.2

theorem groundInitialTask_source
    {P G r μ A Labels δ i j a b : ZFSet.{u}}
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels)
    (first : ZFSet.pair i a ∈ literalTaskSourceGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels)
    (second : ZFSet.pair j b ∈ literalTaskSourceGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) : a = b := by
  have transport := ((triple_mem_taskTransportGraph G
    (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels A δ i j).1 task).2.2.2
  exact transport.source_eq first second

theorem groundInitialTask_intertwine
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one δ i j S S' q x y : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels)
      (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair i S ∈ Maps → ZFSet.pair j S' ∈ Maps →
      ZFSet.pair q x ∈ S → ZFSet.pair q y ∈ S' →
      ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  intro first second image image'
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  have firstEq := ((entries i S).1 first).2
  have secondEq := ((entries j S').1 second).2
  exact M.groundEligibleBatchAction_equivariant group action meet task
    (firstEq ▸ image) (secondEq ▸ image')

end PartitionPilot.Forcing.TransitiveGround

end OAI
