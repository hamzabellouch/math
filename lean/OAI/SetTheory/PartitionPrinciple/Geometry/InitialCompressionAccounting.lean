import OAI.SetTheory.PartitionPrinciple.Definability.RepresentativeProductAgreement
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundEligibleBatchActionRecognition

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

structure GroundCompressionState (M : TransitiveGround.{u})
    {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
    (seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters) where
  data : RecursiveStateData.{u}
  batch : AttachmentBatchInputs data.D data.rD data.μD data.J
    data.Qs data.rs data.μs data.As data.Es data.Fs data.Ss
  inputs : CodedRecursiveMapInputs batch I data.Maps Sources Reps G m inv one data.A
  task : CodedRecursiveTaskAction inputs T
  invariant : RecursiveCompressionInvariant seed inputs
  ground : RecursiveGroundFields M inputs

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem inputs_toState : state.inputs.toState = state.data := by
  cases state with
  | mk data batch inputs task invariant ground => cases data; rfl

theorem code_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    state.data.code ∈ M.sets := by
  rw [← state.inputs_toState]
  exact M.recursiveStateCode_mem pairing state.ground.carrier state.ground.order
    state.ground.meet state.ground.indices state.ground.spaces state.ground.relations
    state.ground.meets state.ground.anchors state.ground.embeddings state.ground.filters
    state.ground.separators state.ground.maps state.ground.action

theorem exists_successor
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ result : GroundCompressionState M seed,
      result.data = state.data.successor M I Sources Reps G T := by
  obtain ⟨next, inputs, task, invariant, ground⟩ := state.invariant.exists_groundNext state.task M
    pairing unions powers separation state.ground hI hSources hReps hG hT
  let result : GroundCompressionState M seed :=
    ⟨inputs.toState, next, inputs, task, invariant, ground⟩
  refine ⟨result, ?_⟩
  change inputs.toState = state.data.successor M I Sources Reps G T
  exact (state.inputs.toState_successor M next inputs).trans
    (congrArg (fun data => data.successor M I Sources Reps G T) state.inputs_toState)

theorem successor_unique_data {first second : GroundCompressionState M seed}
    (hfirst : first.data = state.data.successor M I Sources Reps G T)
    (hsecond : second.data = state.data.successor M I Sources Reps G T) :
    first.data = second.data := hfirst.trans hsecond.symm

end GroundCompressionState

end

section
universe u

def FiniteCompressionAccounting (P0 I Sources τ : ZFSet.{u}) (data : RecursiveStateData.{u}) : Prop :=
  ∀ x ∈ data.currentCarrier, x ∈ P0 ∨
    ∃ i ∈ I, ∃ S a k b, ∃ y ∈ data.D,
      ZFSet.pair i S ∈ data.Maps ∧ ZFSet.pair i a ∈ Sources ∧
      ZFSet.pair τ k ∈ S ∧ ZFSet.pair a b ∈ S ∧ ZFSet.pair y x ∈ S ∧
      ZFSet.pair x k ∈ data.currentOrder ∧ ZFSet.pair x b ∉ data.currentOrder

namespace CodedRecursiveMapInputs
variable {P0 τ D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem accounting_next
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T))
    (hτ : τ ∈ D) (top : ∀ x ∈ D, ZFSet.pair x τ ∈ rD)
    (accounted : FiniteCompressionAccounting P0 I Sources τ h.toState) :
    FiniteCompressionAccounting P0 I Sources τ inputs.toState := by
  intro x hx
  change x ∈ next.batchCarrier at hx
  obtain ⟨X, rfl⟩ := h.nextEncode_surjective M next x hx
  cases X with
  | inl X =>
    rw [h.nextEncode_old]
    rcases accounted (d.coding.encode X) (d.coding.encode_mem X) with original | accounted
    · exact Or.inl original
    · obtain ⟨i, hi, S, a, k, b, y, hy, indexed, source, cap, base, image, lower, outside⟩ := accounted
      have function := (h.valid i S indexed).injection.function
      have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
      have hk := (ZFSet.pair_mem_prod.1 (function.1 cap)).2
      have hb := (ZFSet.pair_mem_prod.1 (function.1 base)).2
      refine Or.inr ⟨i, hi, h.liftSection M next i, a, k, b, y,
        old_mem_taggedExtension hy, (entries _ _).2 ⟨hi, rfl⟩, source,
        (h.liftSection_old_iff M next indexed hτ).2 cap,
        (h.liftSection_old_iff M next indexed ha).2 base,
        (h.liftSection_old_iff M next indexed hy).2 image, ?_, ?_⟩
      · exact (next.old_order_iff (d.coding.encode_mem X) hk).2 lower
      · exact fun nextLower => outside ((next.old_order_iff (d.coding.encode_mem X) hb).1 nextLower)
  | inr q =>
    obtain ⟨i, y, image, below, outside⟩ := h.toInputs.fresh_accounting
      ⟨τ, hτ⟩ (fun x => top x.val x.property) q
    let S := h.maps.value i
    let k := d.coding.encode ((h.toInputs.previous i).toFun ⟨τ, hτ⟩)
    let b := d.coding.encode ((h.toInputs.previous i).toFun (h.toInputs.source i))
    have indexed : ZFSet.pair i.val S ∈ Maps := h.maps.value_entry i
    have cap : ZFSet.pair τ k ∈ S := h.toInputs_previous_entry i ⟨τ, hτ⟩
    have base : ZFSet.pair (h.source i).val b ∈ S :=
      h.toInputs_previous_entry i (h.source i)
    refine Or.inr ⟨i.val, i.property, h.liftSection M next i.val, (h.source i).val, k, b,
      d.coding.encode y, d.coding.encode_mem y,
      (entries _ _).2 ⟨i.property, rfl⟩, h.source_entry i,
      (h.liftSection_old_iff M next indexed hτ).2 cap,
      (h.liftSection_old_iff M next indexed (h.source i).property).2 base, ?_, ?_, ?_⟩
    · have lifted := h.liftSection_entry M next i y
      exact image ▸ lifted
    · exact (h.next_le_encode M next (.inr q) (.inl ((h.toInputs.previous i).toFun ⟨τ, hτ⟩))).2 below
    · exact fun lower => outside ((h.next_le_encode M next (.inr q)
        (.inl ((h.toInputs.previous i).toFun (h.toInputs.source i)))).1 lower)

end CodedRecursiveMapInputs

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionInvariant
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
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
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ Maps ∈ M.sets ∧
      B ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ inputs : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one B,
          RecursiveCompressionInvariant seed inputs ∧ CodedRecursiveTaskAction inputs T := by
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
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, valid, hB, currentAction,
    Reps, hReps, reps, represents, agreement⟩ :=
    M.exists_groundInitialRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet
  let inputs : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one B :=
    ⟨maps, (fields 0).2, reps, group, currentAction, valid, agreement⟩
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
  exact ⟨hI, (fields 0).1, (fields 4).1, hMaps, hB,
    M.groundTaskTransport_mem pairing unions powers separation hP hG hr hμ hA hLabels meet,
    Reps, hReps, seed, inputs, invariant,
    M.groundInitialTaskAction pairing unions powers separation hP hG hr hμ hA hLabels
      group action meet Reps inputs⟩

noncomputable def initialCompressionData (P G r μ A Labels : ZFSet.{u}) : RecursiveStateData.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Sources := literalTaskSourceGraph I P R U Labels
  let Base := literalTaskBaseGraph I P R U Labels
  { D := P
    rD := r
    μD := μ
    J := I
    Qs := constantFamilyGraph I P
    rs := constantFamilyGraph I r
    μs := constantFamilyGraph I μ
    As := Sources
    Es := Base
    Fs := literalTaskFilterGraph I P R U Labels
    Ss := literalTaskSeparatorGraph I P R U Labels
    Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) Sources Base
    A := M.groundEligibleBatchAction P G r μ A Labels }

theorem exists_groundInitialCompressionState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ G ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ state : GroundCompressionState M seed,
          state.data = M.initialCompressionData P G r μ A Labels := by
  obtain ⟨hI, hSources, hFilters, hMaps, hB, hT, Reps, hReps, seed, inputs, invariant, task⟩ :=
    M.exists_groundInitialCompressionInvariant pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  obtain ⟨_, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have ground : RecursiveGroundFields M inputs :=
    ⟨hP, hr, hμ, hI, hQs, hrs, hμs, hSources, (fields 2).1, hFilters,
      (fields 3).1, hMaps, hB⟩
  let state : GroundCompressionState M seed :=
    ⟨inputs.toState, _, inputs, task, invariant, ground⟩
  exact ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, rfl⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def initialCompressionFieldsFormula {n} (fields : Fin 13 → Fin n)
    (P G r μ A Labels : Fin n) : SetFormula n :=
  .conj (.equal (fields 0) P) (.conj (.equal (fields 1) r) (.conj (.equal (fields 2) μ)
    (.conj (groundEligibleTasksFormula (fields 3) P G r μ A Labels)
      (.conj (constantFamilySetFormula (fields 4) (fields 3) P)
        (.conj (constantFamilySetFormula (fields 5) (fields 3) r)
          (.conj (constantFamilySetFormula (fields 6) (fields 3) μ)
            (.conj (groundLiteralTaskFieldFormula 0 (fields 7) (fields 3) P r μ Labels)
              (.conj (groundLiteralTaskFieldFormula 2 (fields 8) (fields 3) P r μ Labels)
                (.conj (groundLiteralTaskFieldFormula 4 (fields 9) (fields 3) P r μ Labels)
                  (.conj (groundLiteralTaskFieldFormula 3 (fields 10) (fields 3) P r μ Labels)
                    (.conj (M.batchEmbeddingFamilyFormula pairing unions powers separation
                      (fields 11) (fields 3) P (fields 4) (fields 5) (fields 7) (fields 8))
                      (M.groundEligibleBatchActionFormula pairing unions powers separation
                        (fields 12) P G r μ A Labels))))))))))))

theorem realize_initialCompressionFieldsFormula {n} (fields : Fin 13 → Fin n)
    (P G r μ A Labels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (M.initialCompressionFieldsFormula pairing unions powers separation fields P G r μ A Labels) env ↔
      (fun j => env (fields j)) = (M.initialCompressionData (env P) (env G) (env r) (env μ) (env A) (env Labels)).field := by
  simp only [initialCompressionFieldsFormula, Realize]
  rw [M.realize_groundEligibleTasksFormula pairing unions powers separation
      (fields 3) P G r μ A Labels env members meet,
    M.realize_constantFamilySetFormula pairing unions powers separation (fields 4) (fields 3) P env members,
    M.realize_constantFamilySetFormula pairing unions powers separation (fields 5) (fields 3) r env members,
    M.realize_constantFamilySetFormula pairing unions powers separation (fields 6) (fields 3) μ env members,
    M.realize_groundLiteralTaskFieldFormula pairing unions powers separation 0 (fields 7) (fields 3) P r μ Labels env members meet,
    M.realize_groundLiteralTaskFieldFormula pairing unions powers separation 2 (fields 8) (fields 3) P r μ Labels env members meet,
    M.realize_groundLiteralTaskFieldFormula pairing unions powers separation 4 (fields 9) (fields 3) P r μ Labels env members meet,
    M.realize_groundLiteralTaskFieldFormula pairing unions powers separation 3 (fields 10) (fields 3) P r μ Labels env members meet,
    M.realize_batchEmbeddingFamilyFormula pairing unions powers separation
      (fields 11) (fields 3) P (fields 4) (fields 5) (fields 7) (fields 8) env members,
    M.realize_groundEligibleBatchActionFormula pairing unions powers separation
      (fields 12) P G r μ A Labels env members meet]
  constructor
  · rintro ⟨points, order, meets, tasks, spaces, orders, meetGraphs, sources, bases, filters, separators, maps, action⟩
    rw [tasks] at spaces orders meetGraphs sources bases filters separators maps
    rw [spaces, orders, sources, bases] at maps
    apply funext
    exact (Fin.cases points (Fin.cases order (Fin.cases meets (Fin.cases tasks (Fin.cases spaces (Fin.cases orders (Fin.cases meetGraphs (Fin.cases sources (Fin.cases bases (Fin.cases filters (Fin.cases separators (Fin.cases maps (Fin.cases action (fun i => Fin.elim0 i))))))))))))))
  · intro equal
    have tasks := congrFun equal (3 : Fin 13)
    have spaces := congrFun equal (4 : Fin 13)
    have orders := congrFun equal (5 : Fin 13)
    have sources := congrFun equal (7 : Fin 13)
    have bases := congrFun equal (8 : Fin 13)
    refine ⟨congrFun equal 0, congrFun equal 1, congrFun equal 2, tasks, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, congrFun equal 12⟩
    · rw [tasks]
      exact spaces
    · rw [tasks]
      exact orders
    · rw [tasks]
      exact congrFun equal 6
    · rw [tasks]
      exact sources
    · rw [tasks]
      exact bases
    · rw [tasks]
      exact congrFun equal 9
    · rw [tasks]
      exact congrFun equal 10
    · rw [tasks, spaces, orders, sources, bases]
      exact congrFun equal 11

noncomputable def initialCompressionDataFormula {n} (output P G r μ A Labels : Fin n) : SetFormula n :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex n 13 output) (prefixIndex n 13)).toFormula
    (M.initialCompressionFieldsFormula pairing unions powers separation (prefixIndex n 13)
      (suffixIndex n 13 P) (suffixIndex n 13 G) (suffixIndex n 13 r) (suffixIndex n 13 μ)
      (suffixIndex n 13 A) (suffixIndex n 13 Labels)))

theorem realize_initialCompressionDataFormula {n} (output P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (M.initialCompressionDataFormula pairing unions powers separation output P G r μ A Labels) env ↔
      env output = (M.initialCompressionData (env P) (env G) (env r) (env μ) (env A) (env Labels)).code := by
  unfold initialCompressionDataFormula
  rw [realize_exBlock]
  let initial := M.initialCompressionData (env P) (env G) (env r) (env μ) (env A) (env Labels)
  constructor
  · rintro ⟨fields, fieldMembers, tuple, specified⟩
    have bounds := extendMany_members 13 fields env fieldMembers members
    have tupleEq := (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 output)
      (prefixIndex n 13) _).1 ((BoundedFormula.realize_toFormula M _ _ bounds).1 tuple)
    have fieldsEq := (M.realize_initialCompressionFieldsFormula pairing unions powers separation
      (prefixIndex n 13) (suffixIndex n 13 P) (suffixIndex n 13 G) (suffixIndex n 13 r)
      (suffixIndex n 13 μ) (suffixIndex n 13 A) (suffixIndex n 13 Labels) _ bounds
      (by simpa only [extendMany_suffix] using meet)).1 specified
    simp only [extendMany_prefix, extendMany_suffix] at tupleEq fieldsEq
    rw [fieldsEq] at tupleEq
    exact tupleEq
  · intro equal
    have fieldMembers := M.recursiveStateData_field_mem initial (equal ▸ members output)
    have bounds := extendMany_members 13 initial.field env fieldMembers members
    refine ⟨initial.field, fieldMembers, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 output) (prefixIndex n 13) _).2
      simp only [extendMany_prefix, extendMany_suffix]
      change env output = initial.code
      exact equal
    · apply (M.realize_initialCompressionFieldsFormula pairing unions powers separation
        (prefixIndex n 13) (suffixIndex n 13 P) (suffixIndex n 13 G) (suffixIndex n 13 r)
        (suffixIndex n 13 μ) (suffixIndex n 13 A) (suffixIndex n 13 Labels) _ bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels
    FiniteCompressionAccounting P I Sources τ (M.initialCompressionData P G r μ A Labels) := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let Sources := literalTaskSourceGraph I P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels
  let Es := literalTaskBaseGraph I P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  intro x hx
  change x ∈ d.batchCarrier at hx
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  cases X with
  | inl p => exact Or.inl p.property
  | inr q =>
    let i := q.1
    let S := batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r) Sources Es i.val
    have spaceEq : d.space i = P :=
      ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry i)).2
    have relEq : d.rel i = r :=
      ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry i)).2
    have function : ZFSet.IsFunc P d.batchCarrier S := by
      simpa only [spaceEq] using d.batch_template_fiber_function i
    have anchorP : d.anchor i ∈ P := by
      simpa only [spaceEq] using (d.fiber i).anchor_mem
    obtain ⟨k, cap, _⟩ := function.2 τ hτ
    obtain ⟨b, base, _⟩ := function.2 (d.anchor i) anchorP
    have image : ZFSet.pair q.2.val.val (d.coding.encode (.inr q)) ∈ S := by
      apply (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
      apply (d.batch_template_entry_iff i _ _).2
      exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩, rfl⟩
    have pointP : q.2.val.val ∈ P := by
      have member : q.2.val.val ∈ d.space i := q.2.val.property
      simpa only [spaceEq] using member
    refine Or.inr ⟨i.val, i.property, S, d.anchor i, k, b, q.2.val.val, pointP,
      (entries _ _).2 ⟨i.property, rfl⟩, d.anchor_entry i, cap, base, image, ?_, ?_⟩
    · exact (d.batch_template_order_iff i image cap).2 (relEq.symm ▸ top _ pointP)
    · intro lower
      exact q.2.property ((d.batch_template_order_iff i image base).1 lower)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
