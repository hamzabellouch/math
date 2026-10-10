import OAI.SetTheory.PartitionPrinciple.Forcing.GroundEligibleActionStep
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchEmbeddingRecognition

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem RestrictedActionCode.base_action_iff
    {P G m one r A g source target base x y : ZFSet.{u}}
    (code : RestrictedActionCode P r A g source target base)
    (action : PosetActionCode G P m one r A) (hx : x ∈ P)
    (below : ZFSet.pair x source ∈ r) :
    ZFSet.pair x y ∈ base ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  constructor
  · intro entry
    have hy := (ZFSet.pair_mem_prod.1 (code.shape entry)).2
    exact ((code.entries x hx y hy).1 entry).2
  · intro entry
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
    exact (code.entries x hx y hy).2 ⟨below, entry⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEligibleTask_representative_base_iff
    {P G r μ A Labels m inv one i g a x y : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (represented : TaskRepresentative P r A (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels i g)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (hx : x ∈ P) (below : ZFSet.pair x a ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair x y ∈ batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) i ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  obtain ⟨a', ha, c, hc, base, hb, s, hs, F, hF, label, hl, equal, restriction⟩ := represented
  have aEq : a = a' := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (equal ▸ source)).2
  have anchorEq : d.anchor j = a := d.anchors.unique (d.anchor_entry j) source
  have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
  have baseEntry : ZFSet.pair i base ∈ literalTaskBaseGraph I P
      (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨equal ▸ hi, rfl⟩
  have baseEq : d.embed j = base := d.embeddings.unique (d.embed_entry j) baseEntry
  have notFresh : x ∉ freshPart (d.space j) (d.rel j) (d.anchor j) := by
    intro fresh
    exact ((mem_freshPart _ _ _ _).1 fresh).2 (relEq.symm ▸ anchorEq.symm ▸ below)
  rw [M.groundEligibleBatchAction_old_iff hx]
  rw [pair_mem_batchTemplateGraph]
  change (ZFSet.pair (ZFSet.pair j.val x) y ∈ _ ↔ _)
  rw [d.batch_template_entry_iff, baseEq]
  have onlyBase : (ZFSet.pair x y ∈ base ∨
      x ∈ freshPart (d.space j) (d.rel j) (d.anchor j) ∧
        y = ZFSet.pair P (ZFSet.pair j.val x)) ↔ ZFSet.pair x y ∈ base :=
    ⟨fun h => h.elim id (fun h => False.elim (notFresh h.1)), Or.inl⟩
  exact onlyBase.trans (restriction.base_action_iff action hx (aEq ▸ below))

theorem exists_groundInitialRepresentatives
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
    let Qs := constantFamilyGraph I P
    let rs := constantFamilyGraph I r
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P Qs rs As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    Maps ∈ M.sets ∧ FunctionGraphOn I Maps ∧
      (∀ i S, ZFSet.pair i S ∈ Maps →
        MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph S) ∧
      B ∈ M.sets ∧ PosetActionCode G d.batchCarrier m one d.batchOrder B ∧
      ∃ representatives ∈ M.sets, ZFSet.IsFunc I G representatives ∧
        (∀ i g, ZFSet.pair i g ∈ representatives → TaskRepresentative P r A R U Labels i g) ∧
        (∀ i a g S x y, ZFSet.pair i a ∈ As → ZFSet.pair i g ∈ representatives →
          ZFSet.pair i S ∈ Maps → x ∈ P → ZFSet.pair x a ∈ r →
            (ZFSet.pair x y ∈ S ↔ ZFSet.pair (ZFSet.pair g x) y ∈ B)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  obtain ⟨representatives, ground, function, represents, _⟩ :=
    M.exists_groundTaskRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels meet
  refine ⟨hMaps, maps, ?_,
    M.groundEligibleBatchAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet,
    M.groundEligibleBatchAction_code pairing unions powers separation hP hG hA group action meet,
    representatives, ground, function, represents, ?_⟩
  · intro i S entry
    obtain ⟨hi, equal⟩ := (entries i S).1 entry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
    have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
    have meetEq : d.meet j = μ := ((pair_mem_constantFamilyGraph I μ _ _).1 (d.meet_entry j)).2
    rw [equal]
    simpa only [spaceEq, relEq, meetEq] using d.batch_template_embedding_code j
  · intro i a g S x y source representative mapEntry hx below
    obtain ⟨hi, equal⟩ := (entries i S).1 mapEntry
    rw [equal]
    exact M.groundEligibleTask_representative_base_iff group action meet hi
      (represents i g representative) source hx below

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
