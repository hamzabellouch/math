import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowRelationSpaces
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundTestedMeetFilters
import OAI.SetTheory.PartitionPrinciple.Geometry.EligibleTaskCovariance
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchAttachment

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem PosetActionCode.raw_fixes_top {G P m inv e r A g T : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (group : GroupCode G m inv e)
    (order : PartialOrderCode P r) (hg : g ∈ G) (hT : T ∈ P)
    (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    ZFSet.pair (ZFSet.pair g T) T ∈ A := by
  obtain ⟨y, entry, _⟩ := action.function.2 (ZFSet.pair g T)
    (ZFSet.pair_mem_prod.2 ⟨hg, hT⟩)
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
  obtain ⟨x, hx, preimage⟩ := action.raw_preimage group hg hT
  have lower := (action.raw_order_iff group order hg preimage entry).2 (greatest x hx)
  have equal : y = T := order.antisymm y hy T hT (greatest y hy) lower
  exact equal ▸ entry

theorem EligibleTaskCode.source_proper
    {G P m inv e r μ A source target base separator F T : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A source target base separator F)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    ZFSet.pair source T ∈ r ∧ ZFSet.pair T source ∉ r := by
  refine ⟨greatest source code.source_mem, ?_⟩
  intro lower
  have sourceEq : source = T := meet.order.antisymm source code.source_mem T hT
    (greatest source code.source_mem) lower
  obtain ⟨g, hg, restriction⟩ := code.representative
  have topEntry := action.raw_fixes_top group meet.order hg hT greatest
  have targetEntry : ZFSet.pair (ZFSet.pair g T) target ∈ A := sourceEq ▸ restriction.target_entry
  obtain ⟨y, _, unique⟩ := action.function.2 (ZFSet.pair g T)
    (ZFSet.pair_mem_prod.2 ⟨hg, hT⟩)
  have targetEq : target = T := (unique target targetEntry).trans (unique T topEntry).symm
  exact code.strict (targetEq.symm ▸ greatest separator code.separator_mem)






theorem eligibleTaskBatchInputs
    {P G r μ A R U Labels m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := eligibleTaskSet P G r μ A R U Labels
    AttachmentBatchInputs P r μ I
      (constantFamilyGraph I P) (constantFamilyGraph I r) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
      (literalTaskFilterGraph I P R U Labels) (literalTaskSeparatorGraph I P R U Labels) := by
  let I := eligibleTaskSet P G r μ A R U Labels
  have subset : I ⊆ literalTaskBound P R U Labels := eligibleTaskSet_subset P G r μ A R U Labels
  refine ⟨meet, ⟨_, constantFamilyGraph_function I P⟩,
    ⟨_, constantFamilyGraph_function I r⟩, ⟨_, constantFamilyGraph_function I μ⟩,
    ⟨_, literalTaskFieldGraph_function subset 0⟩, ⟨_, literalTaskFieldGraph_function subset 2⟩,
    ⟨_, literalTaskFieldGraph_function subset 4⟩, ⟨_, literalTaskFieldGraph_function subset 3⟩, ?_⟩
  intro i hi Q r' μ' a' base' F' e' hQ hr hμ ha' hBase' hF' he'
  obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 hQ).2
  obtain rfl := ((pair_mem_constantFamilyGraph I r _ r').1 hr).2
  obtain rfl := ((pair_mem_constantFamilyGraph I μ _ μ').1 hμ).2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 0).1 ha').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 2).1 hBase').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 4).1 hF').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 3).1 he').2
  obtain ⟨g, hg, represented⟩ := code.representative
  exact represented.singleAttachmentInputs group action meet hg ha hc code.filter he
    code.lower code.strict code.upper

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundEligibleTasks (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  eligibleTaskSet P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels

theorem groundEligibleTasks_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleTasks P G r μ A Labels ∈ M.sets := by
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation hP hP
  have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation hP hr hμ meet
  let params := extend P (extend G (extend r (extend μ (extend A
    (extend R (extend U (extend Labels Fin.elim0)))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hμ (Fin.cases hA
      (Fin.cases hR (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) params members
    (M.literalTaskBound_mem pairing unions powers separation hP hR hU hLabels)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (literalTaskBound P R U Labels) = M.groundEligibleTasks P G r μ A Labels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_eligibleTaskEntryFormula _ _ _ _ _ _ _ _ _ _ meet]
    exact ⟨And.right, fun hz => ⟨eligibleTaskSet_subset P G r μ A R U Labels hz, hz⟩⟩
  exact equal ▸ selected

theorem literalTaskCode_mem_groundEligibleTasks
    (P G r μ A Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ M.groundEligibleTasks P G r μ A Labels ↔
      label ∈ Labels ∧ base ∈ M.sets ∧ F ∈ M.sets ∧ EligibleTaskCode P G r μ A a c base e F := by
  rw [groundEligibleTasks, literalTaskCode_mem_eligibleTaskSet,
    M.mem_groundRelations, M.mem_groundMeetFilters]
  constructor
  · rintro ⟨_, _, ⟨hBase, _⟩, _, ⟨hF, _⟩, hLabel, code⟩
    exact ⟨hLabel, hBase, hF, code⟩
  · rintro ⟨hLabel, hBase, hF, code⟩
    obtain ⟨g, _, represented⟩ := code.representative
    exact ⟨code.source_mem, code.target_mem, ⟨hBase, represented.shape⟩,
      code.separator_mem, ⟨hF, code.filter⟩, hLabel, code⟩






theorem groundEligibleTaskFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    I ∈ M.sets ∧ constantFamilyGraph I P ∈ M.sets ∧
      constantFamilyGraph I r ∈ M.sets ∧ constantFamilyGraph I μ ∈ M.sets ∧
      ∀ j : Fin 6, literalTaskFieldGraph I P R U Labels j ∈ M.sets ∧
        ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  exact ⟨hI, M.constantFamilyGraph_mem pairing unions powers separation hI hP,
    M.constantFamilyGraph_mem pairing unions powers separation hI hr,
    M.constantFamilyGraph_mem pairing unions powers separation hI hμ,
    M.literalTaskFieldFamilies pairing unions powers separation hI hP hR hU hLabels
      (eligibleTaskSet_subset P G r μ A _ _ Labels)⟩

theorem groundEligibleTaskBatchInputs
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    AttachmentBatchInputs P r μ I
      (constantFamilyGraph I P) (constantFamilyGraph I r) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
      (literalTaskFilterGraph I P R U Labels) (literalTaskSeparatorGraph I P R U Labels) :=
  eligibleTaskBatchInputs group action meet

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem literalTaskBound_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P R U Labels : ZFSet.{u}} (points : ZFSet.rank P < o) (relations : ZFSet.rank R < o)
    (filters : ZFSet.rank U < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (literalTaskBound P R U Labels) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit relations (rank_product_lt limit points (rank_product_lt limit filters labels))))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundPower_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A : ZFSet.{u}} (bound : ZFSet.rank A < o) : ZFSet.rank (M.groundPower A) < o := by
  have subset : M.groundPower A ⊆ ZFSet.powerset A := fun _ hz => (ZFSet.mem_sep.1 hz).1
  have rankBound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at rankBound
  exact rankBound.trans_lt (limit.succ_lt bound)

theorem groundRelations_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B : ZFSet.{u}} (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank (M.groundRelations A B) < o :=
  M.groundPower_rank_lt limit (rank_product_lt limit source target)

theorem groundMeetFilters_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P : ZFSet.{u}} (r μ : ZFSet.{u}) (points : ZFSet.rank P < o) :
    ZFSet.rank (M.groundMeetFilters P r μ) < o :=
  (ZFSet.rank_mono (show M.groundMeetFilters P r μ ⊆ M.groundPower P
    from fun _ hz => (ZFSet.mem_sep.1 hz).1)).trans_lt (M.groundPower_rank_lt limit points)

theorem groundEligibleTasks_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P Labels : ZFSet.{u}} (G r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (M.groundEligibleTasks P G r μ A Labels) < o :=
  (ZFSet.rank_mono (eligibleTaskSet_subset P G r μ A (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels)).trans_lt
      (literalTaskBound_rank_lt limit points (M.groundRelations_rank_lt limit points points)
        (M.groundMeetFilters_rank_lt limit r μ points) labels)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem taskRepresentativeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P G r A R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hA : A ∈ M.sets)
    (hR : R ∈ M.sets) (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) :
    taskRepresentativeRelation I P G r A R U Labels ∈ M.sets := by
  let params := extend I (extend P (extend G (extend r (extend A
    (extend R (extend U (extend Labels Fin.elim0)))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hA
      (Fin.cases hR (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taskRepresentativeEntryFormula 0 1 2 3 4 5 6 7 8) params members
    (M.prod_mem pairing unions powers separation hI hG)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taskRepresentativeEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod I G) = taskRepresentativeRelation I P G r A R U Labels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taskRepresentativeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taskRepresentativeEntryFormula _ _ _ _ _ _ _ _ _ _)
  exact equal ▸ selected

theorem exists_groundTaskRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    ∃ representatives ∈ M.sets, ZFSet.IsFunc I G representatives ∧
      (∀ task g, ZFSet.pair task g ∈ representatives →
        TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels task g) ∧
      (∀ a c base e F label g, ZFSet.pair (literalTaskCode a c base e F label) g ∈ representatives →
        RestrictedActionCode P r A g a c base) := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  obtain ⟨representatives, ground, function, subset⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hG
    (M.taskRepresentativeRelation_mem pairing unions powers separation hI hP hG hr hA hR hU hLabels)
    (eligibleTask_representative_total P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
  have represents : ∀ task g, ZFSet.pair task g ∈ representatives →
      TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels task g :=
    fun _ _ entry => ((pair_mem_taskRepresentativeRelation _ _ _ _ _ _ _ _ _ _).1 (subset entry)).2.2
  exact ⟨representatives, ground, function, represents,
    fun _ _ _ _ _ _ _ entry => (represents _ _ entry).restriction⟩






theorem groundEligibleTaskAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
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
    let μs := constantFamilyGraph I μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Fs := literalTaskFilterGraph I P R U Labels
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧
      batchAttachmentShadowGraph I P Qs μs As Es ∈ M.sets ∧
      batchAttachmentTemplateGraph I P Qs rs As Es ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧
      MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph ∧
      ZFSet.IsFunc (indexedAttachmentDomain I Qs) P (batchAttachmentShadowGraph I P Qs μs As Es) ∧
      ZFSet.IsFunc (indexedAttachmentDomain I Qs) d.batchCarrier
        (batchAttachmentTemplateGraph I P Qs rs As Es) ∧
      MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph (attachmentOldEmbeddingGraph P) ∧
      (∀ p ∈ P, ZFSet.pair p p ∈ attachmentOldEmbeddingGraph P) ∧
      d.batchOrder = codedAttachmentOrder P (indexedAttachmentFresh I Qs rs As) r
        (batchAttachmentInsideGraph I Qs rs) (batchAttachmentShadowGraph I P Qs μs As Es)
        (batchAttachmentUpperGraph I P Qs Fs) ∧
      (∀ i : {i : ZFSet.{u} // i ∈ I},
        batchTemplateGraph I P Qs rs As Es i.val ∈ M.sets ∧
        MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph
          (batchTemplateGraph I P Qs rs As Es i.val)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hL, hrL, hμL, hShadow, hRepresentation, hOld⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hP hr hI hQs hrs hμs
    (fields 0).1 (fields 2).1 (fields 4).1
  refine ⟨hL, hrL, hμL, hShadow, hRepresentation, hOld,
    d.batch_meetOrder, d.batch_shadow_function, d.batch_template_function,
    d.coding.old_embedding_code,
    (fun p hp => (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨hp, rfl⟩), rfl, ?_⟩
  intro i
  have hSpace : d.space i = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry i)).2
  have hRel : d.rel i = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry i)).2
  have hMeet : d.meet i = μ := ((pair_mem_constantFamilyGraph I μ _ _).1 (d.meet_entry i)).2
  refine ⟨M.batchTemplateGraph_mem pairing unions powers separation hI hP hQs hrs
    (fields 0).1 (fields 2).1 (M.transitive hI i.property), ?_⟩
  simpa only [hSpace, hRel, hMeet] using d.batch_template_embedding_code i

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundBelow
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem meetFilters {P r μ K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (strong : GroundStrongLimit M K) (small : GroundBelow M P K) :
    GroundBelow M (M.groundMeetFilters P r μ) K :=
  (strong.power_closed pairing unions powers separation hP hK small).restrict separation
    (M.groundMeetFilters_mem powers separation hP hr hμ meet) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

theorem literalTaskBound {P R U Labels K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M P K) (relations : GroundBelow M R K)
    (filters : GroundBelow M U K) (labels : GroundBelow M Labels K) :
    GroundBelow M (Forcing.literalTaskBound P R U Labels) K := by
  have combine {X Y : ZFSet.{u}} (first : X ∈ M.sets ∧ GroundBelow M X K)
      (second : Y ∈ M.sets ∧ GroundBelow M Y K) :
      ZFSet.prod X Y ∈ M.sets ∧ GroundBelow M (ZFSet.prod X Y) K :=
    ⟨M.prod_mem pairing unions powers separation first.1 second.1,
      GroundBelow.product pairing unions powers separation first.1 second.1 hK ordinal strong first.2 second.2⟩
  exact (combine ⟨hP, points⟩ (combine ⟨hP, points⟩ (combine ⟨hR, relations⟩
    (combine ⟨hP, points⟩ (combine ⟨hU, filters⟩ ⟨hLabels, labels⟩))))).2

end GroundBelow

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundEligibleTasks_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M P K) (labels : GroundBelow M Labels K) :
    GroundBelow M (M.groundEligibleTasks P G r μ A Labels) K := by
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  have relations := GroundBelow.relations pairing unions powers separation hP hP hK ordinal strong points points
  have filters := GroundBelow.meetFilters pairing unions powers separation hP hr hμ hK meet strong points
  have bound := GroundBelow.literalTaskBound pairing unions powers separation hP hR hU hLabels hK
    ordinal strong points relations filters labels
  exact bound.restrict separation
    (M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet) hK
    (eligibleTaskSet_subset P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

def eligibleTaskCap (P T i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair P (ZFSet.pair i T)

namespace TransitiveGround

variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
  (meet : MeetOrderCode P r μ) (hT : T ∈ P)
  (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT greatest

theorem groundEligibleTask_cap_fresh {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    ZFSet.pair i T ∈ indexedAttachmentFresh (M.groundEligibleTasks P G r μ A Labels)
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) P)
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) r)
      (literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  exact (literalTask_fresh_iff ha hc hb hs hF hl).2
    ⟨hi, hT, (code.source_proper group action meet hT greatest).2⟩

theorem groundEligibleTask_cap_entry {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair (ZFSet.pair i T) (eligibleTaskCap P T i) ∈
      batchAttachmentTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT greatest hi
  exact (pair_mem_batchAttachmentTemplateGraph _ _ _ _ _ _ _ _ _).2
    ⟨indexedAttachmentFresh_subset _ _ _ _ fresh, pair_mem_taggedExtension.2 fresh,
      Or.inr ⟨fresh, rfl⟩⟩

theorem groundEligibleTask_cap_mem {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    eligibleTaskCap P T i ∈ (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchCarrier :=
  pair_mem_taggedExtension.2 (M.groundEligibleTask_cap_fresh group action meet hT greatest hi)

omit group action in
theorem groundEligibleTask_cap_shadow {i c : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair (ZFSet.pair i T) c ∈ batchAttachmentShadowGraph I P
      (constantFamilyGraph I P) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  obtain ⟨a, ha, b, hb, base, hbase, s, hs, F, hF, label, hl, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hb hbase hs hF hl 1).1 target).2
  have topMeet : ZFSet.pair (ZFSet.pair T a) a ∈ μ := meet.pair_iff.2
    ⟨hT, ha, ha, greatest a ha, meet.order.refl a ha,
      fun _ _ _ lower => lower⟩
  obtain ⟨g, _, represented⟩ := code.representative
  have baseEntry := (represented.entries a ha c hb).2
    ⟨meet.order.refl a ha, represented.target_entry⟩
  exact (literalTask_shadow_iff ha hb hbase hs hF hl).2
    ⟨hi, (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).2
      ⟨hT, hb, a, ha, topMeet, baseEntry⟩⟩

theorem groundEligibleTask_negative_cap {i c F v w : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (hv : v ∈ P) (negative : v ∉ F)
    (entry : ZFSet.pair (ZFSet.pair (eligibleTaskCap P T i) v) w ∈
      (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchMeetGraph) :
    ZFSet.pair (ZFSet.pair c v) w ∈ μ ∧ ZFSet.pair w c ∈ r ∧
      ZFSet.pair w c ∈ (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchOrder := by
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ M.groundEligibleTasks P G r μ A Labels} := ⟨i, hi⟩
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT greatest hi
  have freshT : T ∈ freshPart (d.space j) (d.rel j) (d.anchor j) :=
    (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
      (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have shadow := M.groundEligibleTask_cap_shadow meet hT greatest hi target
  have hc := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 shadow)).2
  have filterEq : d.filter j = F := (d.filters.unique filter (d.filter_entry j)).symm
  have notAbove : ZFSet.pair (eligibleTaskCap P T i) v ∉ d.batchOrder := by
    intro lower
    have positive := (d.batch_old_upper_iff j freshT hv).1 lower
    exact negative (filterEq ▸ positive)
  obtain ⟨z, oldMeet, _⟩ := meet.operation.2 (ZFSet.pair c v)
    (ZFSet.pair_mem_prod.2 ⟨hc, hv⟩)
  have newMeet := d.batch_shadow_meet_code j freshT hv shadow oldMeet notAbove
  obtain ⟨_, _, unique⟩ := d.batch_meetOrder.operation.2
    (ZFSet.pair (eligibleTaskCap P T i) v)
    (ZFSet.pair_mem_prod.2 ⟨M.groundEligibleTask_cap_mem group action meet hT greatest hi,
      old_mem_taggedExtension hv⟩)
  have equal : w = z := (unique w entry).trans (unique z newMeet).symm
  have oldW : ZFSet.pair (ZFSet.pair c v) w ∈ μ := equal.symm ▸ oldMeet
  have lower := meet.lower_left c v w oldW
  have hw := (ZFSet.pair_mem_prod.1 (meet.operation.1 oldW)).2
  exact ⟨oldW, lower, (d.coding.le_encode (.inl ⟨w, hw⟩) (.inl ⟨c, hc⟩)).2 lower⟩

end TransitiveGround






noncomputable def initialCapGraph (I L T representation : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ k ∈ L, z = ZFSet.pair i k ∧
    ZFSet.pair (ZFSet.pair i T) k ∈ representation) (ZFSet.prod I L)

theorem mem_initialCapGraph (I L T representation z : ZFSet.{u}) :
    z ∈ initialCapGraph I L T representation ↔
      ∃ i ∈ I, ∃ k ∈ L, z = ZFSet.pair i k ∧
        ZFSet.pair (ZFSet.pair i T) k ∈ representation := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨i, hi, k, hk, rfl, entry⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hk⟩, i, hi, k, hk, rfl, entry⟩

theorem pair_mem_initialCapGraph (I L T representation i k : ZFSet.{u}) :
    ZFSet.pair i k ∈ initialCapGraph I L T representation ↔
      i ∈ I ∧ k ∈ L ∧ ZFSet.pair (ZFSet.pair i T) k ∈ representation := by
  rw [mem_initialCapGraph]
  constructor
  · rintro ⟨j, hj, z, hz, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hz, entry⟩
  · rintro ⟨hi, hk, entry⟩
    exact ⟨i, hi, k, hk, rfl, entry⟩

theorem initialCapGraph_function {I L T representation domain : ZFSet.{u}}
    (function : ZFSet.IsFunc domain L representation)
    (covers : ∀ i ∈ I, ZFSet.pair i T ∈ domain) :
    ZFSet.IsFunc I L (initialCapGraph I L T representation) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  obtain ⟨k, entry, unique⟩ := function.2 (ZFSet.pair i T) (covers i hi)
  have hk := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  refine ⟨k, (pair_mem_initialCapGraph _ _ _ _ _ _).2 ⟨hi, hk, entry⟩, ?_⟩
  intro z hz
  exact unique z ((pair_mem_initialCapGraph _ _ _ _ _ _).1 hz).2.2

namespace BoundedFormula

open SetFormula

def initialCapEntryFormula {n} (z I L T representation : Fin n) : BoundedFormula n :=
  exMem I (exMem L.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (tripleMembershipFormula 1 T.succ.succ 0 representation.succ.succ)))

theorem truth_initialCapEntryFormula {n} (z I L T representation : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (initialCapEntryFormula z I L T representation) env ↔
      env z ∈ initialCapGraph (env I) (env L) (env T) (env representation) := by
  simp only [initialCapEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula, mem_initialCapGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem initialCapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I L T representation : ZFSet.{u}}
    (hI : I ∈ M.sets) (hL : L ∈ M.sets) (hT : T ∈ M.sets)
    (hRepresentation : representation ∈ M.sets) :
    initialCapGraph I L T representation ∈ M.sets := by
  let params := extend I (extend L (extend T (extend representation Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hL (Fin.cases hT (Fin.cases hRepresentation (fun i => Fin.elim0 i))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.initialCapEntryFormula 0 1 2 3 4) params members
    (M.prod_mem pairing unions powers separation hI hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.initialCapEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I L) = initialCapGraph I L T representation := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_initialCapEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

noncomputable def groundEligibleTaskCaps (P G r μ A Labels T : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Qs := constantFamilyGraph I P
  let rs := constantFamilyGraph I r
  let As := literalTaskSourceGraph I P R U Labels
  let Es := literalTaskBaseGraph I P R U Labels
  initialCapGraph I (taggedExtension P (indexedAttachmentFresh I Qs rs As)) T
    (batchAttachmentTemplateGraph I P Qs rs As Es)

theorem groundEligibleTaskCaps_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    M.groundEligibleTaskCaps P G r μ A Labels T ∈ M.sets ∧
      ZFSet.IsFunc I d.batchCarrier (M.groundEligibleTaskCaps P G r μ A Labels T) ∧
      (∀ i k, ZFSet.pair i k ∈ M.groundEligibleTaskCaps P G r μ A Labels T ↔
        i ∈ I ∧ k = eligibleTaskCap P T i) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hL, _, _, _, hRepresentation, _⟩ := M.groundEligibleTaskAttachment
    pairing unions powers separation hP hG hr hμ hA hLabels group action meet
  have graphMem := M.initialCapGraph_mem pairing unions powers separation
    hI hL (M.transitive hP hT) hRepresentation
  have function : ZFSet.IsFunc I d.batchCarrier (M.groundEligibleTaskCaps P G r μ A Labels T) := by
    apply initialCapGraph_function d.batch_template_function
    intro i hi
    exact indexedAttachmentFresh_subset _ _ _ _
      (M.groundEligibleTask_cap_fresh group action meet hT greatest hi)
  refine ⟨graphMem, function, ?_⟩
  intro i k
  change ZFSet.pair i k ∈ initialCapGraph _ _ _ _ ↔ _
  rw [pair_mem_initialCapGraph]
  constructor
  · rintro ⟨hi, _, entry⟩
    have capEntry := M.groundEligibleTask_cap_entry group action meet hT greatest hi
    have domain := (ZFSet.pair_mem_prod.1 (d.batch_template_function.1 entry)).1
    obtain ⟨_, _, unique⟩ := d.batch_template_function.2 (ZFSet.pair i T) domain
    exact ⟨hi, (unique k entry).trans (unique _ capEntry).symm⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨hi, M.groundEligibleTask_cap_mem group action meet hT greatest hi,
      M.groundEligibleTask_cap_entry group action meet hT greatest hi⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
