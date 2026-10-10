import OAI.SetTheory.PartitionPrinciple.Forcing.GroundChronologicalTransitionTransport
import OAI.SetTheory.PartitionPrinciple.Geometry.OldProfilePreservationComposition
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOmegaOneTaskBearingSuccessorFunction

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I : Type v} [Small.{u} I] [Preorder I] [Finite I]

local instance : Finite (MainTransitionIndex I) := by
  classical
  let := Fintype.ofFinite I
  infer_instance

noncomputable def ofFinite (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j)
    (ground : ZFSet.range key ∈ M.sets) (ordinal : ordinalSetProperty (ZFSet.range key))
    (diagram : GroundChronologicalMainDiagram M C D rD pairing unions powers separation I)
    (linked : I → GroundLinkedMainStage M K Labels C D rD)
    (same : ∀ i, (linked i).main = diagram.stage i) (coverage : diagram.CoversOldBirths) :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation I where
  key := key
  key_injective := injective
  key_order := order
  indices_ground := ground
  indices_ordinal := ordinal
  diagram := diagram
  linked := linked
  linked_main := same
  coverage := coverage
  stages_ground := familyCodeGraph_finite_ground pairing unions ⟨_, ground⟩ key _
    (fun i => M.transitive ground (ZFSet.mem_range.2 ⟨i, rfl⟩))
    (fun i => (linked i).code_ground pairing)
  transitions_ground := familyCodeGraph_finite_ground pairing unions ⟨_, ground⟩ _ _
    (fun p => M.orderedPair_mem pairing
      (M.transitive ground (ZFSet.mem_range.2 ⟨p.val.2, rfl⟩))
      (M.transitive ground (ZFSet.mem_range.2 ⟨p.val.1, rfl⟩)))
    (fun p => (diagram.transition p.property).map.code_mem pairing)

variable {pairing unions powers separation}
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
variable (conditions : GroundInaccessibleConditions M K)
variable (keys : ∀ i, ZFSet.rank (run.key i) < ZFSet.rank K)
include infinite hK conditions keys

theorem finite_stageGraph_rank_lt : ZFSet.rank run.stageGraph < ZFSet.rank K :=
  familyCodeGraph_finite_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    run.key _ keys (fun i => (run.linked i).code_rank_lt pairing unions powers separation infinite hK conditions)

omit keys [Finite I] in
theorem transition_code_rank_lt {i j : I} (before : i ≤ j) :
    ZFSet.rank (run.diagram.transition before).map.code < ZFSet.rank K := by
  have invariants (k : I) : (run.diagram.stage k).Invariant K Labels :=
    run.linked_main k ▸ (run.linked k).invariant
  exact (run.diagram.transition before).map.code_rank_lt_inaccessible
    pairing unions powers separation infinite hK conditions
    (invariants i).points_rank (invariants j).points_rank
    (invariants i).actors_rank (invariants j).actors_rank

theorem finite_transitionGraph_rank_lt : ZFSet.rank run.transitionGraph < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact familyCodeGraph_finite_rank_lt limit _ _
    (fun p => rank_orderedPair_lt limit (keys p.val.2) (keys p.val.1))
    (fun p => run.transition_code_rank_lt infinite hK conditions p.property)

theorem finite_code_rank_lt : ZFSet.rank run.code < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (rank_finiteCodeRange_lt limit run.key keys)
      (Fin.cases (run.finite_stageGraph_rank_lt infinite hK conditions keys)
        (fun _ => run.finite_transitionGraph_rank_lt infinite hK conditions keys)))

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (first second : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition first.main second.main)
variable (coverage : step.CoversOldBirths)

noncomputable def twoStage :
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2) := by
  have empty : (∅ : ZFSet.{u}) ∈ M.sets :=
    M.empty_mem ⟨first.main.cutoff, first.main.cutoff_ground⟩
  have one := M.insert_mem pairing unions empty empty
  have two := M.insert_mem pairing unions one one
  have ground : ZFSet.range (@finiteMainIndexKey.{u} 2) ∈ M.sets := by
    simpa only [finiteMainIndexKey_range, natSetCode_succ, natSetCode_zero] using two
  have ordinal : ordinalSetProperty (ZFSet.range (@finiteMainIndexKey.{u} 2)) := by
    rw [finiteMainIndexKey_range]
    exact ordinalSetProperty_succ (ordinalSetProperty_succ ordinalSetProperty_empty)
  apply ofFinite pairing unions powers separation finiteMainIndexKey
    (finiteMainIndexKey_injective 2) finiteMainIndexKey_order ground ordinal
    (GroundChronologicalMainDiagram.twoStage pairing unions powers separation step)
    (Fin.cases first (fun _ => second))
  · intro i
    cases i using Fin.cases <;> rfl
  · exact GroundChronologicalMainDiagram.twoStage_coversOldBirths
      pairing unions powers separation step coverage

theorem twoStage_indices :
    (twoStage pairing unions powers separation first second step coverage).indices = natSetCode 2 :=
  finiteMainIndexKey_range 2

theorem twoStage_linked_zero :
    (twoStage pairing unions powers separation first second step coverage).linked 0 = first := rfl

theorem twoStage_linked_one :
    (twoStage pairing unions powers separation first second step coverage).linked 1 = second := rfl

theorem twoStage_stage_zero :
    (twoStage pairing unions powers separation first second step coverage).diagram.stage 0 = first.main := rfl

theorem twoStage_stage_one :
    (twoStage pairing unions powers separation first second step coverage).diagram.stage 1 = second.main := rfl

theorem twoStage_transition_zero_one :
    (twoStage pairing unions powers separation first second step coverage).diagram.transition
      (show (0 : Fin 2) ≤ 1 from by decide) = step := rfl

theorem twoStage_stageGraph_zero (z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 0) z ∈
      (twoStage pairing unions powers separation first second step coverage).stageGraph ↔ z = first.code :=
  (twoStage pairing unions powers separation first second step coverage).stageGraph_entry 0 z

theorem twoStage_stageGraph_one (z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 1) z ∈
      (twoStage pairing unions powers separation first second step coverage).stageGraph ↔ z = second.code :=
  (twoStage pairing unions powers separation first second step coverage).stageGraph_entry 1 z

theorem twoStage_transitionGraph_zero_one (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈
      (twoStage pairing unions powers separation first second step coverage).transitionGraph ↔ z = step.map.code :=
  (twoStage pairing unions powers separation first second step coverage).transitionGraph_entry
    (show (0 : Fin 2) ≤ 1 from by decide) z

theorem twoStage_code_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ZFSet.rank (twoStage pairing unions powers separation first second step coverage).code < ZFSet.rank K := by
  apply (twoStage pairing unions powers separation first second step coverage).finite_code_rank_lt
    infinite hK conditions
  intro i
  exact rank_natSetCode_lt (conditions.rank_isLimit pairing unions powers separation infinite hK) i.val

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target first second : GroundChronologicalMainStage M C D rD}

def PreservesOldProfiles (transition : GroundChronologicalMainTransition source target) : Prop :=
  OldProfilePreservationCode source.stage.carrier source.stage.order source.stage.meetGraph
    target.stage.carrier target.stage.order target.stage.meetGraph transition.map.points
    (M.groundPower source.stage.carrier)

theorem identity_preservesOldProfiles
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (stage : GroundChronologicalMainStage M C D rD) :
    (identity pairing unions powers separation stage).PreservesOldProfiles :=
  OldProfilePreservationCode.identity stage.stage.carrier stage.stage.order stage.stage.meetGraph
    (M.groundPower stage.stage.carrier)

theorem comp_preservesOldProfiles
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (left : GroundChronologicalMainTransition source middle)
    (right : GroundChronologicalMainTransition middle target)
    (first : left.PreservesOldProfiles) (second : right.PreservesOldProfiles) :
    (left.comp pairing unions powers separation right).PreservesOldProfiles :=
  OldProfilePreservationCode.comp_ground M separation first second middle.stage.carrier_ground
    left.map.points_ground

theorem retargetEq_preservesOldProfiles_iff
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).PreservesOldProfiles ↔ transition.PreservesOldProfiles := by
  cases sourceEqual
  cases targetEqual
  rfl

end GroundChronologicalMainTransition

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem preservesOldProfiles
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) : transition.PreservesOldProfiles :=
  code.old_profiles_on_linked

end TaskBearingMainSuccessorCode
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialTwoStageMainPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ first second : GroundLinkedMainStage M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode),
            ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
              first.main = seed.source ∧ second.main = certificate.target ∧
              first.serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              second.serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
              run.linked 0 = first ∧ run.linked 1 = second ∧
              run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
              (∀ z, ZFSet.pair (natSetCode 0) z ∈ run.stageGraph ↔ z = first.code) ∧
              (∀ z, ZFSet.pair (natSetCode 1) z ∈ run.stageGraph ↔ z = second.code) ∧
              (∀ z, ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈ run.transitionGraph ↔
                z = certificate.transition.map.code) ∧
              (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.points =
                certificate.transition.map.points ∧
              (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.actors =
                certificate.transition.map.actors := by
  dsimp only
  obtain ⟨level, seed, certificate, initial, successor, _candidateGround,
    _initialGround, initialRank, initialMember, initialAgreement,
    _successorGround, successorRank, successorMember, successorAgreement,
    targetInvariant, _transitionRank, _terminal⟩ :=
    M.exists_groundInitialMainSeedSuccessorRanked pairing unions powers separation
      collection infinite choice hK standard
  let first : GroundLinkedMainStage M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) :=
    ⟨seed.source, initial, initialAgreement, seed.invariant, initialRank⟩
  let second : GroundLinkedMainStage M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) :=
    ⟨certificate.target, successor, successorAgreement, targetInvariant, successorRank⟩
  let run := GroundMainPrefix.twoStage pairing unions powers separation first second
    certificate.transition certificate.coversOldBirths
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact ⟨level, seed, certificate, first, second, run, rfl, rfl, initialMember, successorMember,
    GroundMainPrefix.twoStage_indices pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    run.code_ground,
    GroundMainPrefix.twoStage_code_rank_lt pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths infinite hK conditions,
    rfl, rfl, rfl, rfl,
    GroundMainPrefix.twoStage_stageGraph_zero pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    GroundMainPrefix.twoStage_stageGraph_one pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    GroundMainPrefix.twoStage_transitionGraph_zero_one pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    rfl, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

def PreservesOldProfiles : Prop :=
  ∀ (i j : I) (before : i ≤ j), (run.diagram.transition before).PreservesOldProfiles

theorem restrict_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    {S : ZFSet.{u}} (subset : S ⊆ run.indices) (ground : S ∈ M.sets)
    (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).PreservesOldProfiles := by
  intro i j before
  exact preserved i.val j.val before

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2))

theorem zero_key_of_two_indices (indices : run.indices = natSetCode 2) :
    run.key 0 = natSetCode 0 := by
  have member : natSetCode 0 ∈ run.indices := by
    rw [indices]
    exact (natSetCode_mem_iff 0 2).2 (by decide)
  obtain ⟨i, equal⟩ := ZFSet.mem_range.1 member
  obtain equalKeys | below := (run.key_order 0 i).1 (Fin.zero_le i)
  · exact equalKeys.trans equal
  · rw [equal] at below
    exact False.elim (ZFSet.notMem_empty _ below)

theorem exists_initialRestriction (indices : run.indices = natSetCode 2)
    (preserved : run.PreservesOldProfiles)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (oldRank : ZFSet.rank run.code < o) :
    ∃ initial : GroundMainPrefix M K Labels C D rD pairing unions powers separation
        {i : Fin 2 // run.key i ∈ natSetCode 1},
      initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
      ZFSet.rank initial.code < o ∧
      initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
      initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
      (∀ i, initial.linked i = run.linked i.val) ∧
      ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = run.diagram.stage 0 := by
  have oneMember : natSetCode 1 ∈ run.indices := by
    rw [indices]
    exact (natSetCode_mem_iff 1 2).2 (by decide)
  have subset : natSetCode 1 ⊆ run.indices := by
    intro x hx
    rw [indices]
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode x 1).1 hx
    exact (natSetCode_mem_iff n 2).2 (by omega)
  have ground := M.transitive run.indices_ground oneMember
  have ordinal := ordinalSetProperty_member run.indices_ordinal oneMember
  let initial := run.restrict subset ground ordinal
  have zeroMember : run.key 0 ∈ natSetCode 1 := by
    rw [run.zero_key_of_two_indices indices]
    exact (natSetCode_mem_iff 0 1).2 (by decide)
  exact ⟨initial, run.restrict_indices subset ground ordinal,
    run.restrict_preservesOldProfiles preserved subset ground ordinal,
    run.restrict_code_rank_lt subset ground ordinal limit oldRank,
    run.restrict_stageGraph subset ground ordinal,
    run.restrict_transitionGraph subset ground ordinal, fun _ => rfl,
    ⟨0, zeroMember⟩, run.zero_key_of_two_indices indices, rfl⟩

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem appendCone_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    (target : GroundLinkedMainStage M K Labels C D rD) (cone : run.diagram.Cone target.main)
    {row : ZFSet.{u}} (ground : row ∈ M.sets)
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
    (covered : cone.append.CoversOldBirths) (legs : ∀ i, (cone.leg i).PreservesOldProfiles) :
    (run.appendCone target cone ground function entries covered).PreservesOldProfiles := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation target.main
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top => exact legs i
    | coe j => exact preserved i j (WithTop.coe_le_coe.mp before)

theorem appendLast_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
    (covered : step.CoversOldBirths) (stepPreserved : step.PreservesOldProfiles) :
    (run.appendLast last greatest target step covered).PreservesOldProfiles := by
  intro i j before
  cases i with
  | top =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation target.main
    | coe j => exact False.elim (WithTop.not_top_le_coe j before)
  | coe i =>
    cases j with
    | top =>
      exact GroundChronologicalMainTransition.comp_preservesOldProfiles
        pairing unions powers separation (run.diagram.transition (greatest i)) step
        (preserved i last (greatest i)) stepPreserved
    | coe j => exact preserved i j (WithTop.coe_le_coe.mp before)

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}

theorem preservesOldProfiles_of_zero_one
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2))
    (crossing : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).PreservesOldProfiles) :
    run.PreservesOldProfiles := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro before
      rw [run.diagram.self]
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation (run.diagram.stage 0)
    · rw [Fin.eq_zero j]
      intro _
      exact crossing
  · rw [Fin.eq_zero i]
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro before
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) before)
    · rw [Fin.eq_zero j]
      intro before
      rw [run.diagram.self]
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation (run.diagram.stage 1)

theorem twoStage_preservesOldProfiles
    (first second : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition first.main second.main)
    (coverage : step.CoversOldBirths) (preserved : step.PreservesOldProfiles) :
    (twoStage pairing unions powers separation first second step coverage).PreservesOldProfiles :=
  (twoStage pairing unions powers separation first second step coverage).preservesOldProfiles_of_zero_one preserved

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
