import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionOrigins

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionOrigin_of_representatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one τ Reps : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (reps : ZFSet.IsFunc (M.groundEligibleTasks P G r μ A Labels) G Reps)
    (represents : ∀ i g, ZFSet.pair i g ∈ Reps →
      TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels i g) :
    Nonempty (GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
      P r μ A τ (M.groundEligibleTasks P G r μ A Labels)
      (literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
      Reps G m inv one (M.groundTaskTransport P G r μ A Labels)
      (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Sources := literalTaskSourceGraph I P R U Labels
  let Filters := literalTaskFilterGraph I P R U Labels
  let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
    (constantFamilyGraph I r) Sources (literalTaskBaseGraph I P R U Labels)
  let B := M.groundEligibleBatchAction P G r μ A Labels
  let T := M.groundTaskTransport P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  have hB := M.groundEligibleBatchAction_mem pairing unions powers separation
    hP hG hr hμ hA hLabels meet
  have currentAction : PosetActionCode G d.batchCarrier m one d.batchOrder B :=
    M.groundEligibleBatchAction_code pairing unions powers separation
    hP hG hA group action meet
  have valid : ∀ i S, ZFSet.pair i S ∈ Maps →
      MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph S := by
    intro i S entry
    obtain ⟨hi, equal⟩ := (entries i S).1 entry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
    have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
    have meetEq : d.meet j = μ := ((pair_mem_constantFamilyGraph I μ _ _).1 (d.meet_entry j)).2
    rw [equal]
    simpa only [spaceEq, relEq, meetEq] using d.batch_template_embedding_code j
  have inputs : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one B := by
    refine ⟨maps, (fields 0).2, reps, group, currentAction, valid, ?_⟩
    intro i a g S x y source representative mapEntry hx below
    obtain ⟨hi, equal⟩ := (entries i S).1 mapEntry
    rw [equal]
    exact M.groundEligibleTask_representative_base_iff group action meet hi
      (represents i g representative) source hx below
  have seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters := by
    refine ⟨meet, action, hτ, (fields 0).2, ⟨_, (fields 4).2⟩, ?_, ?_⟩
    · intro δ i j g k product a transport source firstRep secondRep productEntry
      have transported := (triple_mem_taskTransportGraph G I P R U Labels A δ i j).1 transport
      have hg := (ZFSet.pair_mem_prod.1 (reps.1 firstRep)).2
      have hp := (ZFSet.pair_mem_prod.1 (group.mul_function.1 productEntry)).2
      exact transported.2.2.2.representative_product_agreement action transported.1 hg hp
        productEntry (represents i g firstRep) (represents j k secondRep) source
    · intro g k v i j l F oldAgree filter positive first second
      exact M.groundInitialTask_positive_agreement group action meet oldAgree filter positive first second
  have invariant : RecursiveCompressionInvariant seed inputs := by
    refine ⟨fun _ hx => hx, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      ?_, top, ?_, ?_⟩
    · intro g x hx y
      exact M.groundEligibleBatchAction_old_iff hx
    · intro g hg k hk v hv oldAgree
      exact M.groundEligibleBatchAction_agreement pairing unions powers separation
        hP hG hA group action meet hg hk hv oldAgree
    · intro i S a F cap base v w mapEntry source filter capEntry baseEntry hv negative entry
      have hi := inputs.maps.pair_source mapEntry
      obtain ⟨a', ha, c, hc, ell, hell, sep, hsep, F', hF, label, hl, equal, _⟩ :=
        (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
      have target : ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels := by
        rw [equal]
        exact (literalTaskFieldGraph_entry_iff ha hc hell hsep hF hl 1).2 ⟨equal ▸ hi, rfl⟩
      exact M.groundInitialMap_negative_cap pairing unions powers separation
        hP hG hr hμ hA hLabels group action meet hτ top mapEntry source target filter
        capEntry baseEntry hv negative entry
  have ground : RecursiveGroundFields M inputs :=
    ⟨hP, hr, hμ, hI, hQs, hrs, hμs, (fields 0).1, (fields 2).1, (fields 4).1,
      (fields 3).1, hMaps, hB⟩
  let state : GroundCompressionState M seed :=
    ⟨inputs.toState, _, inputs,
      M.groundInitialTaskAction pairing unions powers separation hP hG hr hμ hA hLabels
        group action meet Reps inputs, invariant, ground⟩
  exact ⟨⟨seed, state, rfl⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialCompressionOrigin_of_recognized_representatives
    {n} (Reps P G r μ A Labels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) {m inv one τ : ZFSet.{u}}
    (group : GroupCode (env G) m inv one)
    (action : PosetActionCode (env G) (env P) m one (env r) (env A))
    (meet : MeetOrderCode (env P) (env r) (env μ)) (hτ : τ ∈ env P)
    (top : ∀ x ∈ env P, ZFSet.pair x τ ∈ env r)
    (recognized : Realize M.sets (groundTaskRepresentativesFormula Reps P G r μ A Labels) env) :
    let I := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    Nonempty (GroundCompressionOrigin M
      (M.initialCompressionData (env P) (env G) (env r) (env μ) (env A) (env Labels))
      (env P) (env r) (env μ) (env A) τ I (literalTaskSourceGraph I (env P) R U (env Labels))
      (env Reps) (env G) m inv one
      (M.groundTaskTransport (env P) (env G) (env r) (env μ) (env A) (env Labels))
      (literalTaskFilterGraph I (env P) R U (env Labels))) := by
  have decoded := (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
    Reps P G r μ A Labels env members meet).1 recognized
  exact M.initialCompressionOrigin_of_representatives pairing unions powers separation
    (members P) (members G) (members r) (members μ) (members A) (members Labels)
    group action meet hτ top decoded.1 decoded.2

theorem exists_groundRecognizedTaskRepresentatives
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {n} (P G r μ A Labels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    ∃ Reps ∈ M.sets, Realize M.sets
      (groundTaskRepresentativesFormula 0 P.succ G.succ r.succ μ.succ A.succ Labels.succ)
      (extend Reps env) := by
  obtain ⟨Reps, hReps, function, represents, _⟩ := M.exists_groundTaskRepresentatives
    pairing unions powers separation choice (members P) (members G) (members r)
    (members μ) (members A) (members Labels) meet
  refine ⟨Reps, hReps, ?_⟩
  exact (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
    0 P.succ G.succ r.succ μ.succ A.succ Labels.succ (extend Reps env)
    (Fin.cases hReps members) meet).2 ⟨function, represents⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
