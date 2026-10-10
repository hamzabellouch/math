import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTaskBearingSuccessorDecoding

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

noncomputable def compressionActorFamily (I H generators : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ k ∈ H, z = ZFSet.pair i k ∧
    ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators)
    (ZFSet.prod I H)

theorem pair_mem_compressionActorFamily (I H generators i k : ZFSet.{u}) :
    ZFSet.pair i k ∈ compressionActorFamily I H generators ↔
      i ∈ I ∧ k ∈ H ∧
        ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators := by
  rw [compressionActorFamily, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, entry⟩
  · rintro ⟨hi, hk, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hk⟩, i, hi, k, hk, rfl, entry⟩

namespace BoundedFormula

def compressionActorEntryFormula {n} (z I H generators zero requests : Fin n) : BoundedFormula n :=
  .exMem I (.exMem H.succ (.exMem requests.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (orderedPairFormula 0 zero.succ.succ.succ 2)
        (tripleMembershipFormula 0 zero.succ.succ.succ 1 generators.succ.succ.succ)))))

theorem truth_compressionActorEntryFormula {n} (z I H generators zero requests : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorEntryFormula z I H generators zero requests) env ↔
      ∃ i ∈ env I, ∃ k ∈ env H, ∃ request ∈ env requests,
        env z = ZFSet.pair i k ∧ request = ZFSet.pair (env zero) i ∧
          ZFSet.pair (ZFSet.pair request (env zero)) k ∈ env generators := by
  simp only [compressionActorEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionActorFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I H generators : ZFSet.{u}} (hI : I ∈ M.sets) (hH : H ∈ M.sets) (hGenerators : generators ∈ M.sets) :
    compressionActorFamily I H generators ∈ M.sets := by
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I, hI⟩
  have singleton : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing zero zero
  let requests := ZFSet.prod {natSetCode 0} I
  have hRequests : requests ∈ M.sets := M.prod_mem pairing unions powers separation singleton hI
  let env := extend I (extend H (extend generators (extend (natSetCode 0) (extend requests Fin.elim0))))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hI (Fin.cases hH (Fin.cases hGenerators (Fin.cases zero (Fin.cases hRequests (fun j => Fin.elim0 j)))))
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.compressionActorEntryFormula 0 1 2 3 4 5) env members
    (M.prod_mem pairing unions powers separation hI hH)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.compressionActorEntryFormula 0 1 2 3 4 5) (extend z env))
      (ZFSet.prod I H) = compressionActorFamily I H generators := by
    apply ZFSet.ext
    intro z
    rw [compressionActorFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr Iff.rfl
    rw [BoundedFormula.truth_compressionActorEntryFormula]
    change (∃ i ∈ I, ∃ k ∈ H, ∃ request ∈ requests,
      z = ZFSet.pair i k ∧ request = ZFSet.pair (natSetCode 0) i ∧
        ZFSet.pair (ZFSet.pair request (natSetCode 0)) k ∈ generators) ↔ _
    constructor
    · rintro ⟨i, hi, k, hk, request, _, eq, rfl, entry⟩
      exact ⟨i, hi, k, hk, eq, entry⟩
    · rintro ⟨i, hi, k, hk, eq, entry⟩
      exact ⟨i, hi, k, hk, _, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩, eq, rfl, entry⟩
  exact equal ▸ ground

end TransitiveGround

theorem compressionActorFamily_injection {I P Rectangles H generators : ZFSet.{u}}
    (injection : InjectionCode (externalChildLetters I P Rectangles) H generators) :
    InjectionCode I H (compressionActorFamily I H generators) := by
  refine ⟨⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩, ?_⟩
  · intro i hi
    have child := (compression_child_iff I P Rectangles i (natSetCode 0)).2 ⟨hi, rfl⟩
    obtain ⟨k, entry, unique⟩ := injection.function.2 _ child
    have hk := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    refine ⟨k, (pair_mem_compressionActorFamily I H generators i k).2 ⟨hi, hk, entry⟩, ?_⟩
    intro l candidate
    exact unique l ((pair_mem_compressionActorFamily I H generators i l).1 candidate).2.2
  · intro i j k first second
    have equal := injection.injective _ _ _
      ((pair_mem_compressionActorFamily I H generators i k).1 first).2.2
      ((pair_mem_compressionActorFamily I H generators j k).1 second).2.2
    exact (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).1).2

end

namespace GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {P G r μ A Labels m inv one τ Reps : ZFSet.{u}}
local notation "I" => M.groundEligibleTasks P G r μ A Labels
local notation "R" => M.groundRelations P P
local notation "U" => M.groundMeetFilters P r μ
variable (origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
  P r μ A τ (M.groundEligibleTasks P G r μ A Labels)
  (literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) Reps G m inv one
  (M.groundTaskTransport P G r μ A Labels)
  (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include origin pairing unions powers separation

theorem initial_representatives : TaskRepresentativesCode Reps I P G r A R U Labels := by
  refine ⟨origin.state.inputs.representatives, ?_⟩
  intro i g representative
  have hi := (ZFSet.pair_mem_prod.1 (origin.state.inputs.representatives.1 representative)).1
  obtain ⟨S, mapEntry⟩ := origin.state.inputs.maps.total hi
  have hI : I ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.indices
  have hP : P ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.carrier
  have hQs : constantFamilyGraph I P ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.spaces
  have hrs : constantFamilyGraph I r ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.relations
  have hAs : literalTaskSourceGraph I P R U Labels ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.anchors
  have hEs : literalTaskBaseGraph I P R U Labels ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.embeddings
  have actualMap : ZFSet.pair i S ∈ M.batchEmbeddingFamily I P
      (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using mapEntry
  have mapEq := (((M.batchEmbeddingFamily_spec pairing unions powers separation
    hI hP hQs hrs hAs hEs).2.2 i S).1 actualMap).2
  obtain ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal, eligible⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  obtain ⟨g₀, _, restriction⟩ := eligible.representative
  have represented : TaskRepresentative P r A R U Labels i g₀ :=
    ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal, restriction⟩
  have source : ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb he hF hl 0).2 ⟨equal ▸ hi, rfl⟩
  have agree : ActionAgreementBelow P r A g₀ g a := by
    intro x hx y _ below
    have stored : ZFSet.pair x y ∈ S ↔
        ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
      have hx' : x ∈ origin.state.data.D := by
        simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using hx
      have below' : ZFSet.pair x a ∈ origin.state.data.rD := by
        simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using below
      simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using
        origin.state.inputs.agreement i a g S x y source representative mapEntry hx' below'
    have canonical := M.groundEligibleTask_representative_base_iff (y := y)
      origin.state.inputs.group origin.seed.originalAction origin.seed.originalOrder
      hi represented source hx below
    dsimp only at canonical
    rw [← mapEq] at canonical
    exact ((M.groundEligibleBatchAction_old_iff hx).symm.trans canonical.symm).trans
      (stored.trans (M.groundEligibleBatchAction_old_iff hx))
  refine ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal,
    restriction.shape, ?_, ?_⟩
  · exact (agree a ha c hc (origin.seed.originalOrder.order.refl a ha)).1 restriction.target_entry
  · intro x hx y hy
    constructor
    · intro entry
      obtain ⟨lower, action⟩ := (restriction.entries x hx y hy).1 entry
      exact ⟨lower, (agree x hx y hy lower).1 action⟩
    · rintro ⟨lower, action⟩
      exact (restriction.entries x hx y hy).2 ⟨lower, (agree x hx y hy lower).2 action⟩

theorem identityTask_representative_agreement {c e F label g : ZFSet.{u}}
    (representative : ZFSet.pair (identityInsertionTask P r c e F label) g ∈ Reps) :
    ActionAgreementBelow P r A g one c := by
  have restriction := ((origin.initial_representatives pairing unions powers separation).2
    _ _ representative).restriction
  change RestrictedActionCode P r A g c c (identityIdealGraph P r c) at restriction
  intro x hx y hy lower
  have fixed : ZFSet.pair (ZFSet.pair g x) x ∈ A := restriction.entry_action
    ((pair_mem_identityIdealGraph P r c x x).2 ⟨rfl, hx, lower⟩)
  have oneEntry := origin.seed.originalAction.one x hx
  constructor
  · intro entry
    have equal := (show FunctionGraphOn (ZFSet.prod G P) A from
      ⟨P, origin.seed.originalAction.function⟩).unique entry fixed
    exact equal.symm ▸ oneEntry
  · intro entry
    have equal := (show FunctionGraphOn (ZFSet.prod G P) A from
      ⟨P, origin.seed.originalAction.function⟩).unique entry oneEntry
    exact equal.symm ▸ fixed

end GroundCompressionOrigin

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "P" => source.stage.carrier
local notation "r" => source.stage.order
local notation "I" => source.stage.compressionTasks Labels
local notation "Q" => certificate.target.stage.carrier
local notation "rectangles" => externalRectangles P source.stage.actors r source.stage.meetGraph source.stage.action
local notation "letters" => externalChildLetters I P rectangles
local notation "generators" => M.externalChildGenerators source.stage.actors letters source.stage.multiplication source.stage.identity

omit certificate in
theorem identityInsertion_source_entry {c e F label : ZFSet.{u}}
    (hi : identityInsertionTask P r c e F label ∈ I) :
    ZFSet.pair (identityInsertionTask P r c e F label) c ∈ source.stage.compressionSources Labels := by
  obtain ⟨hc, hc', hb, he, hF, hl, _⟩ := (literalTaskCode_mem_eligibleTaskSet P source.stage.actors r
    source.stage.meetGraph source.stage.action (M.groundRelations P P)
    (M.groundMeetFilters P r source.stage.meetGraph) Labels c c (identityIdealGraph P r c) e F label).1 hi
  exact (literalTaskFieldGraph_entry_iff hc hc' hb he hF hl 0).2 ⟨hi, rfl⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem identityInsertion_representative_image_agreement {c e F label g g' c' : ZFSet.{u}}
    (representative : ZFSet.pair (identityInsertionTask P r c e F label) g ∈ certificate.Reps)
    (actor : ZFSet.pair g g' ∈ certificate.transition.map.actors)
    (image : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ActionAgreementBelow Q certificate.target.stage.order certificate.target.stage.action
      g' certificate.target.stage.identity c' :=
  certificate.transition.map.agreement g source.stage.identity g' certificate.target.stage.identity c c'
    actor certificate.transition.map.group_embedding.one image
    (certificate.origin.identityTask_representative_agreement pairing unions powers separation representative)

variable (infinite : Realize M.sets infinity Fin.elim0)
include infinite

theorem identityInsertion_generator_fixes {c e F label k c' : ZFSet.{u}}
    (hi : identityInsertionTask P r c e F label ∈ I)
    (generator : ZFSet.pair
      (ZFSet.pair (ZFSet.pair (natSetCode 0) (identityInsertionTask P r c e F label)) (natSetCode 0)) k ∈ generators)
    (image : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ∀ z ∈ Q, ZFSet.pair z c' ∈ certificate.target.stage.order →
      ZFSet.pair (ZFSet.pair k z) z ∈ certificate.target.stage.action := by
  obtain ⟨g, representative, _⟩ := certificate.origin.state.inputs.representatives.2 _ hi
  have hg := (ZFSet.pair_mem_prod.1 (certificate.origin.state.inputs.representatives.1 representative)).2
  obtain ⟨g', actor, _⟩ := certificate.transition.map.group_embedding.injection.function.2 g hg
  have first := certificate.compression_generator_full_agreement pairing unions powers separation infinite hi
    (identityInsertion_source_entry hi) representative generator actor image
  have second := certificate.identityInsertion_representative_image_agreement pairing unions powers separation
    representative actor image
  intro z hz lower
  exact (first z hz z hz lower).2 ((second z hz z hz lower).2 (certificate.target.stage.action_code.one z hz))

theorem exists_identityInsertion_actor {c e F label : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets)
    (filter : MeetFilterCode P r source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) (hlabel : label ∈ Labels) :
    ∃ k ∈ certificate.target.stage.actors,
      (∀ c', ZFSet.pair c c' ∈ certificate.transition.map.points →
        ∀ z ∈ Q, ZFSet.pair z c' ∈ certificate.target.stage.order →
          ZFSet.pair (ZFSet.pair k z) z ∈ certificate.target.stage.action) ∧
      ∀ τ' v, ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points →
        (ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
          ZFSet.pair label v ∈ certificate.insertionCapImages c e F) := by
  have hi := M.identityInsertionTask_mem pairing unions powers separation source.stage.carrier_ground
    source.stage.order_ground hF source.stage.action_code source.stage.group_code.identity_mem
    hc he filter lower strict above hlabel
  obtain ⟨k, hk, agreement, top⟩ := certificate.exists_compression_actor pairing unions powers separation infinite hi
  obtain ⟨g, representative, _⟩ := certificate.origin.state.inputs.representatives.2 _ hi
  have hg := (ZFSet.pair_mem_prod.1 (certificate.origin.state.inputs.representatives.1 representative)).2
  obtain ⟨g', actor, _⟩ := certificate.transition.map.group_embedding.injection.function.2 g hg
  refine ⟨k, hk, ?_, ?_⟩
  · intro c' image z hz below
    have first := agreement c g g' c' (identityInsertion_source_entry hi) representative actor image
    have second := certificate.identityInsertion_representative_image_agreement pairing unions powers separation
      representative actor image
    exact (first z hz z hz below).2 ((second z hz z hz below).2 (certificate.target.stage.action_code.one z hz))
  · intro τ' v image
    rw [certificate.insertionCapImages_entry_iff pairing unions powers separation infinite]
    exact (top τ' v image).trans ⟨fun entry => ⟨hlabel, entry⟩, fun entry => entry.2⟩

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "P" => source.stage.carrier
local notation "r" => source.stage.order
local notation "I" => source.stage.compressionTasks Labels
local notation "H" => certificate.target.stage.actors
local notation "rectangles" => externalRectangles P source.stage.actors r source.stage.meetGraph source.stage.action
local notation "letters" => externalChildLetters I P rectangles
local notation "generators" => M.externalChildGenerators source.stage.actors letters source.stage.multiplication source.stage.identity

noncomputable def insertionActorImages (c e F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels I H (identityInsertionTaskGraph Labels I P r c e F)
    (compressionActorFamily I H generators)

theorem insertionActorImages_entry_iff {c e F label k : ZFSet.{u}} :
    ZFSet.pair label k ∈ certificate.insertionActorImages c e F ↔
      label ∈ Labels ∧ ZFSet.pair
        (ZFSet.pair (ZFSet.pair (natSetCode 0) (identityInsertionTask P r c e F label)) (natSetCode 0)) k ∈ generators := by
  have generatorCode : InjectionCode letters H generators := by
    rw [certificate.target_fields.2.2.2.1]
    exact certificate.external.inputs.generators_injection
  rw [insertionActorImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨hlabel, _, task, _, entry, actor⟩
    have equal := ((pair_mem_identityInsertionTaskGraph Labels I P r c e F label task).1 entry).2.2
    exact ⟨hlabel, equal ▸ ((pair_mem_compressionActorFamily I H generators task k).1 actor).2.2⟩
  · rintro ⟨hlabel, generator⟩
    have bounds := ZFSet.pair_mem_prod.1 (generatorCode.function.1 generator)
    have hi := ((compression_child_iff I P rectangles
      (identityInsertionTask P r c e F label) (natSetCode 0)).1 bounds.1).1
    exact ⟨hlabel, bounds.2, _, hi,
      (pair_mem_identityInsertionTaskGraph Labels I P r c e F _ _).2 ⟨hlabel, hi, rfl⟩,
      (pair_mem_compressionActorFamily I H generators _ k).2 ⟨hi, bounds.2, generator⟩⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem insertionActorImages_ground {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets)
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) :
    certificate.insertionActorImages c e F ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels certificate.indices_ground
    certificate.target.stage.actors_ground
    (M.identityInsertionTaskGraph_mem pairing unions powers separation hLabels certificate.indices_ground
      source.stage.carrier_ground source.stage.order_ground hc he hF)
    (M.compressionActorFamily_mem pairing unions powers separation certificate.indices_ground
      certificate.target.stage.actors_ground certificate.external.inputs.generators_ground)

variable {c e F : ZFSet.{u}}

theorem insertionActorImages_injection
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets)
    (filter : MeetFilterCode P r source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    InjectionCode Labels H (certificate.insertionActorImages c e F) := by
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.stage.carrier_ground source.stage.order_ground hF source.stage.action_code
    source.stage.group_code.identity_mem hc he filter lower strict above
  have generatorCode : InjectionCode letters H generators := by
    rw [certificate.target_fields.2.2.2.1]
    exact certificate.external.inputs.generators_injection
  exact tasks.compose (compressionActorFamily_injection generatorCode)

theorem insertionActorImages_function
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets)
    (filter : MeetFilterCode P r source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    ZFSet.IsFunc Labels H (certificate.insertionActorImages c e F) :=
  (certificate.insertionActorImages_injection pairing unions powers separation hc he hF filter lower strict above).function

theorem insertionActorImages_cap_iff
    (infinite : Realize M.sets infinity Fin.elim0) {label k τ' v : ZFSet.{u}}
    (actor : ZFSet.pair label k ∈ certificate.insertionActorImages c e F)
    (imageTop : ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
      ZFSet.pair label v ∈ certificate.insertionCapImages c e F := by
  obtain ⟨hlabel, generator⟩ := certificate.insertionActorImages_entry_iff.1 actor
  have child := (ZFSet.pair_mem_prod.1
    (certificate.external.inputs.generators_injection.function.1 generator)).1
  have hi := ((compression_child_iff I P rectangles
    (identityInsertionTask P r c e F label) (natSetCode 0)).1 child).1
  rw [certificate.insertionCapImages_entry_iff pairing unions powers separation infinite]
  exact (certificate.compression_generator_cap_iff pairing unions powers separation infinite hi generator imageTop).trans
    ⟨fun entry => ⟨hlabel, entry⟩, fun entry => entry.2⟩

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
local notation "P" => source.stage.carrier
local notation "r" => source.stage.order
local notation "I" => source.stage.compressionTasks Labels
local notation "rectangles" => externalRectangles P source.stage.actors r source.stage.meetGraph source.stage.action
include certificate pairing unions powers separation infinite

theorem insertionActorImages_fixes {c e F label k c' : ZFSet.{u}}
    (actor : ZFSet.pair label k ∈ certificate.insertionActorImages c e F)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ∀ z ∈ certificate.target.stage.carrier, ZFSet.pair z c' ∈ certificate.target.stage.order →
      ZFSet.pair (ZFSet.pair k z) z ∈ certificate.target.stage.action := by
  obtain ⟨_, generator⟩ := certificate.insertionActorImages_entry_iff.1 actor
  have child := (ZFSet.pair_mem_prod.1
    (certificate.external.inputs.generators_injection.function.1 generator)).1
  have hi := ((compression_child_iff I P rectangles
    (identityInsertionTask P r c e F label) (natSetCode 0)).1 child).1
  exact certificate.identityInsertion_generator_fixes pairing unions powers separation infinite hi generator imageC

theorem insertionActorImages_below_cap {c e F label k K x x' y : ZFSet.{u}}
    (actor : ZFSet.pair label k ∈ certificate.insertionActorImages c e F)
    (cap : ZFSet.pair label K ∈ certificate.insertionCapImages c e F)
    (image : ZFSet.pair x x' ∈ certificate.transition.map.points)
    (acted : ZFSet.pair (ZFSet.pair k x') y ∈ certificate.target.stage.action) :
    ZFSet.pair y K ∈ certificate.target.stage.order := by
  obtain ⟨_, generator⟩ := certificate.insertionActorImages_entry_iff.1 actor
  have hk : k ∈ certificate.target.stage.actors := by
    rw [certificate.target_fields.2.2.2.1]
    exact (ZFSet.pair_mem_prod.1 (certificate.external.inputs.generators_injection.function.1 generator)).2
  have shape := ZFSet.pair_mem_prod.1 (certificate.transition.map.point_embedding.injection.function.1 image)
  obtain ⟨top', imageTop, _⟩ := certificate.transition.map.point_embedding.injection.function.2
    source.stage.top source.stage.top_mem
  have hTop' := (ZFSet.pair_mem_prod.1
    (certificate.transition.map.point_embedding.injection.function.1 imageTop)).2
  have topAction := (certificate.insertionActorImages_cap_iff pairing unions powers separation infinite actor imageTop).2 cap
  have hy := (ZFSet.pair_mem_prod.1 (certificate.target.stage.action_code.function.1 acted)).2
  have hK := (ZFSet.pair_mem_prod.1 (certificate.target.stage.action_code.function.1 topAction)).2
  have below := certificate.transition.map.point_embedding.monotone x source.stage.top x' top'
    (source.stage.greatest x shape.1) image imageTop
  exact certificate.target.stage.action_code.monotone k hk x' shape.2 top' hTop' y hy K hK acted topAction below

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem successorTaskBindings :
    MainSuccessorTaskBindingsCode M Labels certificate.successorOutputValues :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    certificate.origin.initial_representatives pairing unions powers separation⟩

variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include infinite hLabels

theorem boundSuccessorOutput :
    MainSuccessorOutputCode certificate.successorOutputValues ∧
      MainSuccessorTaskBindingsCode M Labels certificate.successorOutputValues :=
  ⟨certificate.successorOutput pairing unions powers separation infinite hLabels,
    certificate.successorTaskBindings pairing unions powers separation⟩

theorem realize_boundSuccessorOutput :
    Realize M.sets
      (.conj (BoundedFormula.mainSuccessorOutputFormula Fin.succ).toFormula
        (mainSuccessorTaskBindingsFormula 0 Fin.succ))
      (extend Labels certificate.successorOutputValues) := by
  have members : ∀ j, extend Labels certificate.successorOutputValues j ∈ M.sets :=
    Fin.cases hLabels
      (certificate.successorOutputValues_ground pairing unions powers separation infinite hLabels)
  exact ⟨(BoundedFormula.realize_mainSuccessorOutputFormula M Fin.succ
      (extend Labels certificate.successorOutputValues) members).2
      (certificate.successorOutput pairing unions powers separation infinite hLabels),
    (M.realize_mainSuccessorTaskBindingsFormula pairing unions powers separation 0 Fin.succ
      (extend Labels certificate.successorOutputValues) members source.stage.meet).2
      (certificate.successorTaskBindings pairing unions powers separation)⟩

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
local notation "P" => source.stage.carrier
local notation "r" => source.stage.order
local notation "Q" => certificate.target.stage.carrier
local notation "R" => certificate.target.stage.order
local notation "μ" => certificate.target.stage.meetGraph
local notation "H" => certificate.target.stage.actors
local notation "A" => certificate.target.stage.action
local notation "points" => certificate.transition.map.points
include pairing unions powers separation infinite

theorem insertionFulfillment {c e F : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets)
    (filter : MeetFilterCode P r source.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    certificate.insertionCapImages c e F ∈ M.sets ∧
    certificate.insertionActorImages c e F ∈ M.sets ∧
    InjectionCode Labels Q (certificate.insertionCapImages c e F) ∧
    InjectionCode Labels H (certificate.insertionActorImages c e F) ∧
    ∀ c' e', ZFSet.pair c c' ∈ points → ZFSet.pair e e' ∈ points →
      (∀ label k, ZFSet.pair label k ∈ certificate.insertionActorImages c e F →
        ∀ z ∈ Q, ZFSet.pair z c' ∈ R → ZFSet.pair (ZFSet.pair k z) z ∈ A) ∧
      (∀ label k K, ZFSet.pair label k ∈ certificate.insertionActorImages c e F →
        ZFSet.pair label K ∈ certificate.insertionCapImages c e F →
        ∀ x x' y, ZFSet.pair x x' ∈ points → ZFSet.pair (ZFSet.pair k x') y ∈ A →
          ZFSet.pair y K ∈ R) ∧
      (∀ label K, ZFSet.pair label K ∈ certificate.insertionCapImages c e F →
        ZFSet.pair c' K ∈ R ∧ ZFSet.pair K c' ∉ R ∧ ZFSet.pair e' K ∉ R ∧
          CodedInsertionProfile Q R μ c' e' K (relationImage F Q points)) ∧
      (∀ first second K L, ZFSet.pair first K ∈ certificate.insertionCapImages c e F →
        ZFSet.pair second L ∈ certificate.insertionCapImages c e F → first ≠ second →
          ZFSet.pair (ZFSet.pair K L) c' ∈ μ) := by
  refine ⟨certificate.insertionCapImages_ground pairing unions powers separation infinite hLabels hc he hF,
    certificate.insertionActorImages_ground pairing unions powers separation hLabels hc he hF,
    certificate.insertionCapImages_injection pairing unions powers separation infinite
      hc he hF filter lower strict above hLabels,
    certificate.insertionActorImages_injection pairing unions powers separation
      hc he hF filter lower strict above, ?_⟩
  intro c' e' imageC imageE
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro label k actor
    exact certificate.insertionActorImages_fixes pairing unions powers separation infinite actor imageC
  · intro label k K actor cap x x' y image acted
    exact certificate.insertionActorImages_below_cap pairing unions powers separation infinite actor cap image acted
  · intro label K cap
    have profile := certificate.insertionCapImages_profile pairing unions powers separation infinite
      hc he hF filter lower strict above cap imageC imageE
    exact ⟨profile.target_below_cap, profile.cap_not_below_target,
      profile.separator_not_below_cap, profile.profile⟩
  · intro first second K L firstCap secondCap different
    exact certificate.insertionCapImages_meet pairing unions powers separation infinite
      hc he hF filter lower strict above hLabels firstCap secondCap different imageC

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
