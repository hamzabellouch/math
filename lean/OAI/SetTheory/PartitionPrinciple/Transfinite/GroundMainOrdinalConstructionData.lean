import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainConditionalTotality
import OAI.SetTheory.PartitionPrinciple.Transfinite.MainPrefixSelectedTraceLaws

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainOrdinalConstruction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
          ∃ initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation
              {i : Fin 2 // run.key i ∈ natSetCode 1},
            let B := level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode)
            B ∈ M.sets ∧ initial.code ∈ B ∧ initial.indices = natSetCode 1 ∧
            initial.PreservesOldProfiles ∧ initial.code ∈ M.sets ∧
            ZFSet.rank initial.code < ZFSet.rank K ∧
            initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
            initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
            (∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source) ∧
            ∃ f ∈ M.sets,
              ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K C C
                (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode))
                (ZFSet.prod level.carrier level.carrier) f ∧
              f ⊆ M.taskBearingSuccessorRelation
                (M.linkedMainStageCandidates level.carrier K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode))
                level.carrier K C C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
              (∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
                target ∈ M.linkedMainStageCandidates level.carrier K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
                z ∈ level.carrier ∧ TaskBearingMainSuccessorCode M K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
                  ZFSet.omega source target z) ∧
              ∃ g ∈ M.sets, ZFSet.IsFunc B B g ∧
                g ⊆ M.mainPrefixConditionalRelation B K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ZFSet.omega f ∧
                (∀ old next, ZFSet.pair old next ∈ g → next ∈ B ∧
                  MainPrefixConditionalStepCode M K C C
                    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
                    ZFSet.omega f old next) ∧
                ∃ p ∈ M.sets,
                  OrdinalRecursionTrace (MainPrefixTraceStepCode B initial.code g) C p ∧
                  ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode B initial.code g) C q → q = p := by
  dsimp only
  obtain ⟨level, seed, run, initial, domainGround, initialMember, initialIndices,
      profiles, initialGround, initialRank, stageRestriction, transitionRestriction, source⟩ :=
    M.exists_initialRecursionSeed pairing unions powers separation collection infinite choice hK standard
  have columnsGround := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨f, hf, fFunction, fSelected, fEntries⟩ :=
    M.exists_groundOmegaOneTaskBearingSuccessorFunction pairing unions powers separation collection infinite choice
      hK standard seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground
      seed.injection_ground seed.dense (fun x hx => (seed.no_endpoints x hx).2) seed.injection_code level
  obtain ⟨g, hg, gFunction, gSelected, gEntries⟩ :=
    level.exists_groundConditionalPrefixFunction pairing unions powers separation collection infinite choice
      hK standard columnsGround seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground
      rfl hf fFunction fSelected
  let B := level.recursionPrefixes
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
  have seedIndex : MainPrefixAtIndex (insert ∅ ∅) initial.code := by
    refine ⟨initial.stageGraph, initial.transitionGraph, ?_⟩
    change mainPrefixCode initial.indices initial.stageGraph initial.transitionGraph = _
    rw [initialIndices]
    rfl
  have advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next := by
    intro old next T entry index
    obtain ⟨S, E, oldCode⟩ := index
    have branch := (gEntries old next entry).2
    exact ⟨branch.next_fields oldCode, branch.extension⟩
  obtain ⟨p, hp, trace, unique⟩ := M.exists_unique_selectedMainPrefixTrace
    pairing unions powers separation collection infinite hK standard level
    (B := B) rfl domainGround initialMember seedIndex hg gFunction advance
  exact ⟨level, seed, run, initial, domainGround, initialMember, initialIndices,
    profiles, initialGround, initialRank, stageRestriction, transitionRestriction, source,
    f, hf, fFunction, fSelected, fEntries, g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

structure GroundMainOrdinalConstructionData (M : TransitiveGround.{u}) (K C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) where
  level : GroundMainCandidateLevel M K
  seed : GroundInitialMainSeedData M K C
  seedRun : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2)
  initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode) pairing unions powers separation
    {i : Fin 2 // seedRun.key i ∈ natSetCode 1}
  domain : ZFSet.{u}
  domain_eq : domain = level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
    (rationalLtGraph seed.fractionCode)
  domain_ground : domain ∈ M.sets
  initial_member : initial.code ∈ domain
  initial_indices : initial.indices = natSetCode 1
  initial_profiles : initial.PreservesOldProfiles
  initial_rank : ZFSet.rank initial.code < ZFSet.rank K
  initial_stages : initial.stageGraph = graphRestriction (natSetCode 1) seedRun.stageGraph
  initial_transitions : initial.transitionGraph =
    graphRestriction (chronologyPairs (natSetCode 1)) seedRun.transitionGraph
  initial_source : ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source
  successors : ZFSet.{u}
  successors_ground : successors ∈ M.sets
  successors_function : ZFSet.IsFunc
    (M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode)) (ZFSet.prod level.carrier level.carrier) successors
  successors_selected : successors ⊆ M.taskBearingSuccessorRelation
    (M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode)) level.carrier K C C
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
  successors_entries : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ successors →
    target ∈ M.linkedMainStageCandidates level.carrier K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode) ∧ z ∈ level.carrier ∧
      TaskBearingMainSuccessorCode M K C C (rationalCarrier seed.fractionCode)
        (rationalLtGraph seed.fractionCode) ZFSet.omega source target z
  steps : ZFSet.{u}
  steps_ground : steps ∈ M.sets
  steps_function : ZFSet.IsFunc domain domain steps
  steps_selected : steps ⊆ M.mainPrefixConditionalRelation domain K C C
    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ZFSet.omega successors
  steps_entries : ∀ old next, ZFSet.pair old next ∈ steps → next ∈ domain ∧
    MainPrefixConditionalStepCode M K C C (rationalCarrier seed.fractionCode)
      (rationalLtGraph seed.fractionCode) ZFSet.omega successors old next
  history : ZFSet.{u}
  history_ground : history ∈ M.sets
  trace : OrdinalRecursionTrace (MainPrefixTraceStepCode domain initial.code steps) C history
  trace_unique : ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode domain initial.code steps) C q →
    q = history

theorem TransitiveGround.exists_groundMainOrdinalData (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    Nonempty (GroundMainOrdinalConstructionData M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      pairing unions powers separation) := by
  obtain ⟨level, seed, seedRun, initial, domainGround, initialMember, indices, profiles,
      _, rank, stages, transitions, source, f, hf, fFunction, fSelected, fEntries,
      g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩ :=
    M.exists_groundMainOrdinalConstruction pairing unions powers separation collection infinite choice hK standard
  exact ⟨⟨level, seed, seedRun, initial, _, rfl, domainGround, initialMember, indices,
    profiles, rank, stages, transitions, source, f, hf, fFunction, fSelected, fEntries,
    g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩⟩

end PartitionPilot.Forcing

end

end OAI
