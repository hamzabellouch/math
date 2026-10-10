import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixRawCoveredAppend

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_preservedRankedAppendLimit (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : M.groundEmbeddable run.indices ZFSet.omega)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ chronology : data.RankedChronology level,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          target.main = chronology.main ∧
          target.serial.code = chronology.serial.code ∧
          extended.PreservesOldProfiles ∧
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  have below : GroundBelow M run.indices K :=
    ⟨ZFSet.omega, standard.omega_mem pairing unions powers separation hK, indices⟩
  obtain ⟨data⟩ := run.exists_fixedTopMainStage i₀ collection infinite choice columns_eq indices
  obtain ⟨chronology⟩ := data.exists_rankedChronology collection infinite choice hK standard below oldRank level
  let target := chronology.linked infinite choice hK standard below oldRank
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨row, ground, function, entries, rowRank⟩ := run.exists_limitTransitionRow limit oldRank
  have rowEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = (chronology.cone.leg i).map.code := entries
  let extended := run.appendCone target chronology.cone ground function rowEntries chronology.cone_coverage
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendCone_code_rank_lt target chronology.cone ground function rowEntries chronology.cone_coverage
      limit oldRank (target.code_rank_lt pairing unions powers separation infinite hK conditions) rowRank
  have preservedExtended : extended.PreservesOldProfiles :=
    run.appendCone_preservesOldProfiles preserved target chronology.cone ground function
      rowEntries chronology.cone_coverage
      (fun i => chronology.transition_preservesOldProfiles preserved i)
  refine ⟨data, chronology, target, extended, rfl, rfl, preservedExtended,
    rfl, rfl, chronology.main_birth, chronology.code_member,
    run.appendCone_indices target chronology.cone ground function rowEntries chronology.cone_coverage,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    run.appendCone_linked_old target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_linked_top target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_transitionGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    ?_, ?_, ?_⟩
  · intro i j before
    rfl
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i x y entry
    exact data.point_strict_top i entry

theorem exists_preservedRankedAppendLimit_of_indices_mem (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ chronology : data.RankedChronology level,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          target.main = chronology.main ∧
          target.serial.code = chronology.serial.code ∧
          extended.PreservesOldProfiles ∧
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          extended.code ∈ level.preservedMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  obtain ⟨data, chronology, target, extended, result⟩ :=
    run.exists_preservedRankedAppendLimit preserved i₀ collection infinite choice columns_eq
      (M.groundOmegaOne_member_countable pairing unions powers separation collection infinite indices)
      oldRank hK standard level
  obtain ⟨mainEqual, serialEqual, profiles, stageEqual, cutoffEqual, birthEqual, serialMember,
    indexEqual, ground, rank, member, rest⟩ := result
  refine ⟨data, chronology, target, extended, mainEqual, serialEqual, profiles, stageEqual,
    cutoffEqual, birthEqual, serialMember, indexEqual, ?_, ground, rank, member,
    level.prefix_mem_preservedMainPrefixes extended profiles rank, rest⟩
  rw [indexEqual]
  exact M.groundOmegaOne_successor pairing unions powers separation collection infinite indices

theorem exists_coveredPreservedAppendLimit (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ chronology : data.RankedChronology level,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
        ∃ cone : run.diagram.Cone target.main,
          run.LimitCoverage target.main cone ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.code =
              (cone.leg i).map.code) ∧
          target.main = chronology.main ∧
          target.serial.code = chronology.serial.code ∧
          extended.PreservesOldProfiles ∧
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          extended.code ∈ level.preservedMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  obtain ⟨data, chronology, target, extended, mainEqual, serialEqual, preservedExtended,
    stageEqual, cutoffEqual, birthEqual, serialMember, indexEqual, indexMember, ground,
    rank, member, preservedMember, oldLinked, topLinked, stages, stageRestriction,
    transitionRestriction, oldMaps, maps, strict⟩ :=
    run.exists_preservedRankedAppendLimit_of_indices_mem preserved i₀ collection infinite choice
      columns_eq indices oldRank hK standard level
  let cone : run.diagram.Cone target.main := mainEqual.symm ▸ chronology.cone
  have transportCoverage {first second : GroundChronologicalMainStage M C D rD}
      (equal : first = second) (original : run.diagram.Cone first)
      (covered : run.LimitCoverage first original) :
      run.LimitCoverage second (equal ▸ original) := by
    cases equal
    exact covered
  have coverage : run.LimitCoverage target.main cone :=
    transportCoverage mainEqual.symm chronology.cone chronology.limitCoverage
  have transportCode {first second : GroundChronologicalMainStage M C D rD}
      (equal : first = second) (original : run.diagram.Cone first) (i : I) :
      ((equal ▸ original).leg i).map.code = (original.leg i).map.code := by
    cases equal
    rfl
  have exactMaps (i : I) :
      (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.code =
        (cone.leg i).map.code := by
    rw [show (cone.leg i).map.code = (chronology.cone.leg i).map.code from
      transportCode mainEqual.symm chronology.cone i]
    exact congrArg₂ ZFSet.pair (maps i).1 (maps i).2
  exact ⟨data, chronology, target, extended, cone, coverage, exactMaps, mainEqual, serialEqual,
    preservedExtended, stageEqual, cutoffEqual, birthEqual, serialMember, indexEqual, indexMember,
    ground, rank, member, preservedMember, oldLinked, topLinked, stages, stageRestriction,
    transitionRestriction, oldMaps, maps, strict⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
