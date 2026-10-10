import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTaskBearingSuccessorDecoding

namespace OAI

namespace PartitionPilot.Forcing

namespace TaskBearingMainSuccessorCode
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem insertion_data
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    ∃ Caps ∈ M.sets, ∃ Reps ∈ M.sets,
      source.main.stage.compressionTasks Labels ∈ M.sets ∧
      source.main.stage.compressionSources Labels ∈ M.sets ∧
      TaskCapFamilyCode (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
        transition.map.points (source.main.stage.compressionTargets Labels)
        (source.main.stage.compressionSeparators Labels) (source.main.stage.compressionFilters Labels)
        (M.groundPower source.main.stage.carrier) Caps ∧
      TaskRepresentativesCode Reps (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier source.main.stage.actors source.main.stage.order source.main.stage.action
        (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
        (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels ∧
      CompressionActorFulfillmentCode (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier source.main.stage.actors target.main.stage.carrier target.main.stage.actors
        target.main.stage.order target.main.stage.action transition.map.points transition.map.actors
        (source.main.stage.compressionSources Labels) Reps source.main.stage.top Caps := by
  obtain ⟨extra, ground, output, bindings⟩ := code.output_on_linked
  obtain ⟨tasks, sources, targets, separators, filters, families, representatives⟩ := bindings
  change extra 0 = source.main.stage.compressionTasks Labels at tasks
  change extra 1 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 0 at sources
  change extra 2 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 1 at targets
  change extra 3 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 3 at separators
  change extra 4 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 4 at filters
  change extra 5 = M.groundPower source.main.stage.carrier at families
  rw [tasks] at sources targets separators filters
  change extra 1 = source.main.stage.compressionSources Labels at sources
  have caps := output.task_caps
  have actors := output.compression_actors
  change TaskCapFamilyCode (extra 0) source.main.stage.carrier target.main.stage.carrier
    target.main.stage.order target.main.stage.meetGraph transition.map.points
    (extra 2) (extra 3) (extra 4) (extra 5) (extra 7) at caps
  change CompressionActorFulfillmentCode (extra 0) source.main.stage.carrier source.main.stage.actors
    target.main.stage.carrier target.main.stage.actors target.main.stage.order target.main.stage.action
    transition.map.points transition.map.actors (extra 1) (extra 6) source.main.stage.top (extra 7) at actors
  rw [tasks, targets, separators, filters, families] at caps
  rw [tasks, sources] at actors
  exact ⟨extra 7, ground 7, extra 6, ground 6, tasks ▸ ground 0,
    sources ▸ ground 1, caps, representatives, actors⟩

end TaskBearingMainSuccessorCode

section
open SetFormula
universe u

noncomputable def identityTaskCapFamily (Labels I P Q r Caps c e F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels I Q (identityInsertionTaskGraph Labels I P r c e F) Caps

theorem pair_mem_identityTaskCapFamily {Labels I P Q r Caps c e F label cap : ZFSet.{u}}
    (function : ZFSet.IsFunc I Q Caps) :
    ZFSet.pair label cap ∈ identityTaskCapFamily Labels I P Q r Caps c e F ↔
      label ∈ Labels ∧ ZFSet.pair (identityInsertionTask P r c e F label) cap ∈ Caps := by
  rw [identityTaskCapFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hl, _, i, _, entry, image⟩
    have equal := ((pair_mem_identityInsertionTaskGraph Labels I P r c e F label i).1 entry).2.2
    exact ⟨hl, equal ▸ image⟩
  · rintro ⟨hl, image⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 image)
    exact ⟨hl, bounds.2, _, bounds.1,
      (pair_mem_identityInsertionTaskGraph Labels I P r c e F _ _).2 ⟨hl, bounds.1, rfl⟩, image⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem identityTaskCapFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Labels I P Q r Caps c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hr : r ∈ M.sets) (hCaps : Caps ∈ M.sets)
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) :
    identityTaskCapFamily Labels I P Q r Caps c e F ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels hI hQ
    (M.identityInsertionTaskGraph_mem pairing unions powers separation hLabels hI hP hr hc he hF) hCaps

end TransitiveGround

namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD Labels Caps : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)
local notation "P" => source.carrier
local notation "Q" => target.carrier
local notation "I" => source.compressionTasks Labels
local notation "r" => source.order
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (caps : TaskCapFamilyCode (source.compressionTasks Labels) source.carrier target.carrier
  target.order target.meetGraph transition.points (source.compressionTargets Labels)
  (source.compressionSeparators Labels) (source.compressionFilters Labels) (M.groundPower source.carrier) Caps)
include caps pairing unions powers separation

theorem identityTaskCapFamily_function {c e F : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    ZFSet.IsFunc Labels Q (identityTaskCapFamily Labels I P Q r Caps c e F) := by
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.carrier_ground source.order_ground hF source.action_code source.group_code.identity_mem
    hc he filter lower strict above
  exact relationCompose_function_of_subset tasks.function caps.function (fun _ h => h)

theorem identityTaskCapFamily_profile {c e F label cap c' e' : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r)
    (entry : ZFSet.pair label cap ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (imageC : ZFSet.pair c c' ∈ transition.points) (imageE : ZFSet.pair e e' ∈ transition.points) :
    CodedCapProfile Q target.order target.meetGraph c' e' cap (relationImage F Q transition.points) := by
  obtain ⟨hl, capEntry⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry
  have bounds := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry)
  have fields := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl
  exact caps.profiles _ bounds.1 c hc e he F ((M.mem_groundPower P F).2 ⟨hF, filter.subset⟩)
    cap bounds.2 c' (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
    e' (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageE)).2
    (fields 1) (fields 3) (fields 4) capEntry imageC imageE

theorem identityTaskCapFamily_meet {c e F first second cap₁ cap₂ c' : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r)
    (entry₁ : ZFSet.pair first cap₁ ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (entry₂ : ZFSet.pair second cap₂ ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (different : first ≠ second) (imageC : ZFSet.pair c c' ∈ transition.points) :
    ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ target.meetGraph := by
  obtain ⟨hl₁, capEntry₁⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry₁
  obtain ⟨hl₂, capEntry₂⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry₂
  have bounds₁ := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry₁)
  have bounds₂ := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry₂)
  have fields₁ := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl₁
  have fields₂ := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl₂
  exact caps.common_target _ bounds₁.1 _ bounds₂.1 c hc cap₁ bounds₁.2 cap₂ bounds₂.2 c'
    (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
    (fun equal => different (identityInsertionTask_injective P r c e F equal))
    (fields₁ 1) (fields₂ 1) capEntry₁ capEntry₂ imageC

theorem identityTaskCapFamily_injection {c e F : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    InjectionCode Labels Q (identityTaskCapFamily Labels I P Q r Caps c e F) := by
  refine ⟨transition.identityTaskCapFamily_function pairing unions powers separation caps
    hc he hF filter lower strict above, ?_⟩
  intro first second cap firstEntry secondEntry
  by_cases equal : first = second
  · exact equal
  · obtain ⟨c', imageC, _⟩ := transition.point_embedding.injection.function.2 c hc
    obtain ⟨e', imageE, _⟩ := transition.point_embedding.injection.function.2 e he
    have profile := transition.identityTaskCapFamily_profile pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry imageC imageE
    have meet := transition.identityTaskCapFamily_meet pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry secondEntry equal imageC
    exact (profile.cap_not_below_target (target.meet.greatest cap cap c' cap profile.cap_mem meet
      (target.meet.order.refl cap profile.cap_mem) (target.meet.order.refl cap profile.cap_mem))).elim

end GroundMainTransition

end

section
universe u

namespace TaskRepresentative

theorem identityInsertion_agreement {P G r A R U Labels m one c e F label g : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels (identityInsertionTask P r c e F label) g)
    (action : PosetActionCode G P m one r A) : ActionAgreementBelow P r A g one c := by
  have restriction := represented.restriction
  change RestrictedActionCode P r A g c c (identityIdealGraph P r c) at restriction
  intro x hx y _ lower
  have fixed : ZFSet.pair (ZFSet.pair g x) x ∈ A := restriction.entry_action
    ((pair_mem_identityIdealGraph P r c x x).2 ⟨rfl, hx, lower⟩)
  have identity := action.one x hx
  have function : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
  exact ⟨fun entry => (function.unique entry fixed).symm ▸ identity,
    fun entry => (function.unique entry identity).symm ▸ fixed⟩

end TaskRepresentative

namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD Labels Reps Caps : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)

theorem identityCompressionActor_fixes {c e F label k c' : ZFSet.{u}}
    (representatives : TaskRepresentativesCode Reps (source.compressionTasks Labels)
      source.carrier source.actors source.order source.action (M.groundRelations source.carrier source.carrier)
      (M.groundMeetFilters source.carrier source.order source.meetGraph) Labels)
    (hi : identityInsertionTask source.carrier source.order c e F label ∈ source.compressionTasks Labels)
    (actor : CompressionActorCode source.carrier source.actors target.carrier target.actors
      target.order target.action transition.points transition.actors (source.compressionSources Labels)
      Reps source.top Caps (identityInsertionTask source.carrier source.order c e F label) k)
    (imageC : ZFSet.pair c c' ∈ transition.points) :
    ∀ z ∈ target.carrier, ZFSet.pair z c' ∈ target.order →
      ZFSet.pair (ZFSet.pair k z) z ∈ target.action := by
  obtain ⟨hc, hc₂, hb, he, hF, hl, _⟩ := (literalTaskCode_mem_eligibleTaskSet source.carrier source.actors
    source.order source.meetGraph source.action (M.groundRelations source.carrier source.carrier)
    (M.groundMeetFilters source.carrier source.order source.meetGraph) Labels c c
    (identityIdealGraph source.carrier source.order c) e F label).1 hi
  have sourceEntry : ZFSet.pair (identityInsertionTask source.carrier source.order c e F label) c ∈
      source.compressionSources Labels :=
    (literalTaskFieldGraph_entry_iff hc hc₂ hb he hF hl 0).2 ⟨hi, rfl⟩
  obtain ⟨g, repEntry, _⟩ := representatives.1.2 _ hi
  have hg := (ZFSet.pair_mem_prod.1 (representatives.1.1 repEntry)).2
  obtain ⟨g', actorEntry, _⟩ := transition.group_embedding.injection.function.2 g hg
  have hg' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 actorEntry)).2
  have hc' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
  have original := (representatives.2 _ _ repEntry).identityInsertion_agreement source.action_code
  have imageAgreement := transition.agreement g source.identity g' target.identity c c'
    actorEntry transition.group_embedding.one imageC original
  have compressionAgreement := actor.1 c hc g hg g' hg' c' hc' sourceEntry repEntry actorEntry imageC
  intro z hz lower
  exact (compressionAgreement z hz z hz lower).2
    ((imageAgreement z hz z hz lower).2 (target.action_code.one z hz))

end GroundMainTransition
end

namespace TaskBearingMainSuccessorCode
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}
local notation "P" => source.main.stage.carrier
local notation "r" => source.main.stage.order
local notation "Q" => target.main.stage.carrier
local notation "R" => target.main.stage.order
local notation "ν" => target.main.stage.meetGraph
local notation "H" => target.main.stage.actors
local notation "B" => target.main.stage.action
local notation "points" => transition.map.points

theorem exists_insertionFamilies
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets) (hc : c ∈ P) (he : e ∈ P)
    (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.main.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    ∃ capFamily ∈ M.sets, ∃ actorFamily ∈ M.sets,
      InjectionCode Labels Q capFamily ∧ InjectionCode Labels H actorFamily ∧
      (∀ label k top' v, ZFSet.pair label k ∈ actorFamily →
        ZFSet.pair source.main.stage.top top' ∈ points →
        (ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair label v ∈ capFamily)) ∧
      ∀ c' e', ZFSet.pair c c' ∈ points → ZFSet.pair e e' ∈ points →
        (∀ label k, ZFSet.pair label k ∈ actorFamily →
          ∀ z ∈ Q, ZFSet.pair z c' ∈ R → ZFSet.pair (ZFSet.pair k z) z ∈ B) ∧
        (∀ label k cap, ZFSet.pair label k ∈ actorFamily → ZFSet.pair label cap ∈ capFamily →
          ∀ x x' y, ZFSet.pair x x' ∈ points → ZFSet.pair (ZFSet.pair k x') y ∈ B →
            ZFSet.pair y cap ∈ R) ∧
        (∀ label cap, ZFSet.pair label cap ∈ capFamily →
          CodedCapProfile Q R ν c' e' cap (relationImage F Q points)) ∧
        (∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ capFamily →
          ZFSet.pair second cap₂ ∈ capFamily → first ≠ second →
            ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ ν) := by
  obtain ⟨Caps, hCaps, Reps, hReps, hI, hSources, caps, reps, total⟩ := code.insertion_data
  obtain ⟨taskActors, hActors, actorFunction, actorLaws⟩ := M.choose_compressionActorFamily
    pairing unions powers separation choice hI source.main.stage.carrier_ground
    source.main.stage.actors_ground target.main.stage.carrier_ground target.main.stage.actors_ground
    target.main.stage.order_ground target.main.stage.action_ground transition.map.points_ground
    transition.map.actors_ground hSources hReps source.main.stage.top_ground hCaps total
  let I := source.main.stage.compressionTasks Labels
  let capFamily := identityTaskCapFamily Labels I P Q r Caps c e F
  let actorFamily := identityTaskCapFamily Labels I P H r taskActors c e F
  have capGround : capFamily ∈ M.sets := M.identityTaskCapFamily_mem pairing unions powers separation
    hLabels hI source.main.stage.carrier_ground target.main.stage.carrier_ground
    source.main.stage.order_ground hCaps hc he hF
  have actorGround : actorFamily ∈ M.sets := M.identityTaskCapFamily_mem pairing unions powers separation
    hLabels hI source.main.stage.carrier_ground target.main.stage.actors_ground
    source.main.stage.order_ground hActors hc he hF
  have capInjection : InjectionCode Labels Q capFamily := transition.map.identityTaskCapFamily_injection
    pairing unions powers separation caps hc he hF filter lower strict above
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.main.stage.carrier_ground source.main.stage.order_ground hF source.main.stage.action_code
    source.main.stage.group_code.identity_mem hc he filter lower strict above
  have function : ZFSet.IsFunc Labels H actorFamily :=
    relationCompose_function_of_subset tasks.function actorFunction (fun _ h => h)
  have topLaw (label k top' v : ZFSet.{u}) (entry : ZFSet.pair label k ∈ actorFamily)
      (imageTop : ZFSet.pair source.main.stage.top top' ∈ points) :
      ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair label v ∈ capFamily := by
    obtain ⟨hl, actorEntry⟩ := (pair_mem_identityTaskCapFamily actorFunction).1 entry
    have actor := actorLaws _ _ actorEntry
    have htop' := (ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 imageTop)).2
    constructor
    · intro acted
      have hv := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 acted)).2
      exact (pair_mem_identityTaskCapFamily caps.function).2 ⟨hl, (actor.2 top' htop' v hv imageTop).1 acted⟩
    · intro capEntry
      have rawCap := ((pair_mem_identityTaskCapFamily caps.function).1 capEntry).2
      have hv := (ZFSet.pair_mem_prod.1 (caps.function.1 rawCap)).2
      exact (actor.2 top' htop' v hv imageTop).2 rawCap
  have actorInjection : InjectionCode Labels H actorFamily := by
    refine ⟨function, ?_⟩
    intro first second k firstEntry secondEntry
    have hf := (ZFSet.pair_mem_prod.1 (function.1 firstEntry)).1
    have hs := (ZFSet.pair_mem_prod.1 (function.1 secondEntry)).1
    obtain ⟨cap₁, firstCap, _⟩ := capInjection.function.2 first hf
    obtain ⟨cap₂, secondCap, _⟩ := capInjection.function.2 second hs
    obtain ⟨top', imageTop, _⟩ := transition.map.point_embedding.injection.function.2
      source.main.stage.top source.main.stage.top_mem
    have actionFunction : FunctionGraphOn (ZFSet.prod H Q) B := ⟨Q, target.main.stage.action_code.function⟩
    have equal := actionFunction.unique ((topLaw first k top' cap₁ firstEntry imageTop).2 firstCap)
      ((topLaw second k top' cap₂ secondEntry imageTop).2 secondCap)
    exact capInjection.injective first second cap₁ firstCap (equal.symm ▸ secondCap)
  refine ⟨capFamily, capGround, actorFamily, actorGround, capInjection, actorInjection, topLaw, ?_⟩
  intro c' e' imageC imageE
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro label k entry
    have actorEntry := ((pair_mem_identityTaskCapFamily actorFunction).1 entry).2
    have hi := (ZFSet.pair_mem_prod.1 (actorFunction.1 actorEntry)).1
    exact transition.map.identityCompressionActor_fixes reps hi (actorLaws _ _ actorEntry) imageC
  · intro label k cap actorEntry capEntry x x' y image acted
    have hk := (ZFSet.pair_mem_prod.1 (function.1 actorEntry)).2
    have shape := ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 image)
    obtain ⟨top', imageTop, _⟩ := transition.map.point_embedding.injection.function.2
      source.main.stage.top source.main.stage.top_mem
    have htop' := (ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 imageTop)).2
    have topAction := (topLaw label k top' cap actorEntry imageTop).2 capEntry
    have hy := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 acted)).2
    have hcap := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 topAction)).2
    have below := transition.map.point_embedding.monotone x source.main.stage.top x' top'
      (source.main.stage.greatest x shape.1) image imageTop
    exact target.main.stage.action_code.monotone k hk x' shape.2 top' htop' y hy cap hcap acted topAction below
  · intro label cap entry
    exact transition.map.identityTaskCapFamily_profile pairing unions powers separation caps
      hc he hF filter lower strict above entry imageC imageE
  · intro first second cap₁ cap₂ firstEntry secondEntry different
    exact transition.map.identityTaskCapFamily_meet pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry secondEntry different imageC

end TaskBearingMainSuccessorCode

end PartitionPilot.Forcing

end OAI
