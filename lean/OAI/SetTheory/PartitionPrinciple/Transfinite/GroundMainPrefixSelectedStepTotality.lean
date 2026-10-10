import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixRawCoveredAppend
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixSelectedSuccessors

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

def MainPrefixRecursionIndexCode (Omega z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ T ∈ Omega ∧ T ≠ ∅

theorem mainPrefixRecursionIndexCode_iff {Omega T S E : ZFSet.{u}} :
    MainPrefixRecursionIndexCode Omega (mainPrefixCode T S E) ↔ T ∈ Omega ∧ T ≠ ∅ := by
  constructor
  · rintro ⟨T', S', E', equal, member, nonempty⟩
    have same := (mainPrefixCode_inj.1 equal).1
    exact same.symm ▸ ⟨member, nonempty⟩
  · rintro ⟨member, nonempty⟩
    exact ⟨T, S, E, rfl, member, nonempty⟩

namespace SetFormula
def mainPrefixRecursionIndexFormula {n} (Omega z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (BoundedFormula.conj
    (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2))
    (.conj (.mem (field 0) (old Omega)) (.neg (BoundedFormula.emptyFormula (field 0))))).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixRecursionIndexFormula {n} (Omega z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixRecursionIndexFormula Omega z) env ↔
      MainPrefixRecursionIndexCode (env Omega) (env z) := by
  rw [mainPrefixRecursionIndexFormula, realize_exBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (BoundedFormula.conj
        (BoundedFormula.mainPrefixTupleFormula (suffixIndex n 3 z)
          (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2))
        (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 Omega))
          (.neg (BoundedFormula.emptyFormula (prefixIndex n 3 0))))).toFormula
        (extendMany 3 fields env) ↔
      env z = mainPrefixCode (fields 0) (fields 1) (fields 2) ∧
        fields 0 ∈ env Omega ∧ fields 0 ≠ ∅ := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_mainPrefixTupleFormula,
      BoundedFormula.truth_emptyFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields 0, fields 1, fields 2, (actual fields ground).1 recognized⟩
  · rintro ⟨T, S, E, equal, member, nonempty⟩
    have ground := M.mainPrefixCode_fields_mem (equal ▸ members z)
    let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have grounds : ∀ j, fields j ∈ M.sets :=
      Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨fields, grounds, (actual fields grounds).2 ⟨equal, member, nonempty⟩⟩

end TransitiveGround

end

section
open SetFormula
universe u v

def MainPrefixSelectedStepCode (f old next : ZFSet.{u}) : Prop :=
  ∃ b S E S' E' a target z,
    old = mainPrefixCode (insert b b) S E ∧
    next = mainPrefixCode (insert (insert b b) (insert b b)) S' E' ∧
    MainPrefixExtends old next ∧
    ZFSet.pair b a ∈ S ∧ ZFSet.pair a (ZFSet.pair target z) ∈ f ∧
    ZFSet.pair (insert b b) target ∈ S' ∧
    ZFSet.pair (ZFSet.pair (insert b b) b) z ∈ E'

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem appendLast_selectedStepCode (last : I) (greatest : ∀ i, i ≤ last)
    (target : GroundLinkedMainStage M K Labels C D rD)
    (step : GroundChronologicalMainTransition (run.diagram.stage last) target.main)
    (covered : step.CoversOldBirths) {b f : ZFSet.{u}}
    (indices : run.indices = insert b b) (lastKey : run.key last = b)
    (selected : ZFSet.pair (run.linked last).code (ZFSet.pair target.code step.map.code) ∈ f) :
    MainPrefixSelectedStepCode f run.code (run.appendLast last greatest target step covered).code := by
  let extended := run.appendLast last greatest target step covered
  refine ⟨b, run.stageGraph, run.transitionGraph, extended.stageGraph, extended.transitionGraph,
    (run.linked last).code, target.code, step.map.code, ?_, ?_, ?_, ?_, selected, ?_, ?_⟩
  · change mainPrefixCode run.indices run.stageGraph run.transitionGraph = _
    rw [indices]
  · change mainPrefixCode extended.indices extended.stageGraph extended.transitionGraph = _
    rw [run.appendLast_indices last greatest target step covered, indices]
  · apply (mainPrefixExtends_iff_restrictions run.graph_code extended.graph_code).2
    refine ⟨?_, run.appendLast_stageGraph_restrict last greatest target step covered,
      run.appendLast_transitionGraph_restrict last greatest target step covered⟩
    intro x hx
    rw [run.appendLast_indices last greatest target step covered]
    exact ZFSet.mem_insert_iff.2 (Or.inr hx)
  · rw [← lastKey]
    exact (run.stageGraph_entry last _).2 rfl
  · rw [← indices, run.appendLast_stageGraph last greatest target step covered]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  · have entry := (extended.transitionGraph_entry (show (last : WithTop I) ≤ ⊤ from le_top)
      step.map.code).2 (congrArg (fun t => t.map.code)
        (run.appendLast_transition_last last greatest target step covered)).symm
    change ZFSet.pair (ZFSet.pair run.indices (run.key last)) step.map.code ∈ extended.transitionGraph at entry
    rw [indices, lastKey] at entry
    exact entry

end GroundMainPrefix

end

section
open SetFormula SetRealization
universe u v

namespace SetFormula
def mainPrefixRecursionDomainFormula {n} (B Omega z : Fin n) : SetFormula n :=
  .conj (.mem z B) (mainPrefixRecursionIndexFormula Omega z)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixRecursionDomainFormula {n} (B Omega z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixRecursionDomainFormula B Omega z) env ↔
      env z ∈ ZFSet.sep (MainPrefixRecursionIndexCode (env Omega)) (env B) := by
  change (env z ∈ env B ∧ Realize M.sets (mainPrefixRecursionIndexFormula Omega z) env) ↔ _
  rw [ZFSet.mem_sep]
  exact and_congr Iff.rfl (M.realize_mainPrefixRecursionIndexFormula Omega z env members)

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def recursionPrefixes (Omega Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MainPrefixRecursionIndexCode Omega) (level.preservedMainPrefixes Labels C D rD)

theorem mem_recursionPrefixes {Omega Labels C D rD z : ZFSet.{u}} :
    z ∈ level.recursionPrefixes Omega Labels C D rD ↔
      z ∈ level.preservedMainPrefixes Labels C D rD ∧ MainPrefixRecursionIndexCode Omega z :=
  ZFSet.mem_sep

theorem recursionPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K)
    {Omega Labels C D rD : ZFSet.{u}} (hOmega : Omega ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.recursionPrefixes Omega Labels C D rD ∈ M.sets := by
  have hB := level.preservedMainPrefixes_ground pairing unions powers separation collection infinite
    hK ordinal hLabels hC hD hrD
  let params : Fin 1 → ZFSet.{u} := fun _ => Omega
  have ground : ∀ j, params j ∈ M.sets := fun _ => hOmega
  have separated := M.separation_mem separation (mainPrefixRecursionIndexFormula 1 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (mainPrefixRecursionIndexFormula 1 0)
      (extend z params)) (level.preservedMainPrefixes Labels C D rD) =
      level.recursionPrefixes Omega Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, level.mem_recursionPrefixes]
    apply and_congr_right
    intro hz
    exact M.realize_mainPrefixRecursionIndexFormula 1 0 (extend z params)
      (Fin.cases (M.transitive hB hz) ground)
  exact equal ▸ separated

theorem prefix_mem_recursionPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Omega Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (indices : run.indices ∈ Omega) (nonempty : run.indices ≠ ∅) :
    run.code ∈ level.recursionPrefixes Omega Labels C D rD :=
  level.mem_recursionPrefixes.2 ⟨level.prefix_mem_preservedMainPrefixes run preserved rank,
    mainPrefixRecursionIndexCode_iff.2 ⟨indices, nonempty⟩⟩

theorem exists_prefix_of_mem_recursionPrefixes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Omega Labels C D rD z : ZFSet.{u}}
    (member : z ∈ level.recursionPrefixes Omega Labels C D rD) :
    ∃ T ∈ M.sets, T ∈ Omega ∧ T ≠ ∅ ∧ Nonempty (SetMembers T) ∧
      ∃ ordinal : ordinalSetProperty T,
        letI := ordinalMainIndexPreorder ordinal
        ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
          run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles ∧
          ZFSet.rank run.code < ZFSet.rank K := by
  obtain ⟨candidate, indexCode⟩ := level.mem_recursionPrefixes.1 member
  obtain ⟨T, hT, ordinal, run, indices, equal, preserved, rank⟩ :=
    level.exists_preservedPrefix_of_mem pairing unions powers separation candidate
  let := ordinalMainIndexPreorder ordinal
  have index : run.indices ∈ Omega ∧ run.indices ≠ ∅ :=
    mainPrefixRecursionIndexCode_iff.1 (equal.symm ▸ indexCode)
  have actual : T ∈ Omega ∧ T ≠ ∅ := indices ▸ index
  have inhabited : Nonempty (SetMembers T) := by
    classical
    by_contra empty
    apply actual.2
    apply (ZFSet.eq_empty T).2
    intro x hx
    exact empty ⟨SetMembers.ofMem x hx⟩
  exact ⟨T, hT, actual.1, actual.2, inhabited, ordinal, run, indices, equal, preserved, rank⟩

end GroundMainCandidateLevel
end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialRecursionSeed
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
            level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            initial.code ∈ level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
            initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
            initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
            initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
            ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source := by
  dsimp only
  obtain ⟨level, seed, _, run, _, _, indices, preserved, rank, first, _, _⟩ :=
    M.exists_initialPreservedPrefixCandidate pairing unions powers separation collection infinite choice hK standard
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨initial, initialIndices, profiles, initialRank, stages, transitions, _, i, key, stage⟩ :=
    run.exists_initialRestriction indices preserved
      (conditions.rank_isLimit pairing unions powers separation infinite hK) rank
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have indexMember : initial.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
    apply ((M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.1 _).2
    refine ⟨initial.indices_ground, initial.indices_ordinal, ?_⟩
    rw [initialIndices]
    exact M.natSetCode_countable pairing unions powers separation infinite 1
  have nonempty : initial.indices ≠ ∅ := by
    rw [initialIndices]
    intro equal
    have member := (natSetCode_mem_iff 0 1).2 (by decide)
    rw [equal] at member
    exact ZFSet.notMem_empty _ member
  exact ⟨level, seed, run, initial,
    level.recursionPrefixes_ground pairing unions powers separation collection infinite hK standard.1.1
      hC hC hC seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_recursionPrefixes initial profiles initialRank indexMember nonempty,
    initialIndices, profiles, initial.code_ground, initialRank, stages, transitions,
    i, key, stage.trans first⟩

end TransitiveGround

namespace GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_selectedStepCode
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hLabels : Labels ∈ M.sets)
    (preserved : run.PreservesOldProfiles) (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (member : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    {b f : ZFSet.{u}} (indices : run.indices = insert b b)
    (level : GroundMainCandidateLevel M K)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
    ∃ next ∈ M.sets,
      next ∈ level.recursionPrefixes
        (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD ∧
      MainPrefixSelectedStepCode f run.code next := by
  have lastMember : b ∈ run.indices := by
    rw [indices]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  obtain ⟨last, lastKey⟩ := ZFSet.mem_range.1 lastMember
  have greatest : ∀ i, i ≤ last := by
    intro i
    apply (run.key_order i last).2
    rw [lastKey]
    have hi : run.key i ∈ run.indices := ZFSet.mem_range.2 ⟨i, rfl⟩
    rw [indices] at hi
    exact ZFSet.mem_insert_iff.1 hi
  have sourceMember : (run.linked last).code ∈
      M.linkedMainStageCandidates level.carrier K Labels C D rD :=
    (M.mem_linkedMainStageCandidates level.carrier K Labels C D rD _).2
      ⟨(level.membership _).2 ⟨(run.linked last).code_ground pairing,
        (run.linkedCode_rank_lt_code last).trans oldRank⟩, run.linked last, rfl⟩
  have graph : FunctionGraphOn (M.linkedMainStageCandidates level.carrier K Labels C D rD) f :=
    ⟨ZFSet.prod level.carrier level.carrier, function⟩
  obtain ⟨output, entry⟩ := graph.total sourceMember
  obtain ⟨targetCode, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨target, step, covered, extended, equal, profiles, targetEqual, mapEqual,
      _, ground, rank, _, extendedIndices, _⟩ :=
    run.exists_rankedAppendSelected collection infinite last greatest preserved oldRank hK standard
      hLabels level selected entry
  have chosen : ZFSet.pair (run.linked last).code (ZFSet.pair target.code step.map.code) ∈ f := by
    rw [targetEqual, mapEqual]
    exact entry
  have branch := run.appendLast_selectedStepCode last greatest target step covered indices lastKey chosen
  rw [← equal] at branch
  have newMember : extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
    rw [extendedIndices]
    exact M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  have nonempty : extended.indices ≠ ∅ := by
    rw [extendedIndices]
    exact setSuccessor_ne_empty run.indices
  exact ⟨extended.code, ground, level.prefix_mem_recursionPrefixes extended profiles rank newMember nonempty, branch⟩

end GroundMainPrefix

open SetFormula SetRealization
universe u v w

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitStepCode_of_fields {J : Type w} [Small.{u} J] [Preorder J]
    (target : GroundLinkedMainStage M K Labels C D rD)
    (extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation J)
    (indices : extended.indices = insert run.indices run.indices)
    (extension : MainPrefixExtends run.code extended.code)
    (entry : ZFSet.pair run.indices target.code ∈ extended.stageGraph)
    (coverage : MainLimitCoverageGraphCode run.indices run.stageGraph extended.transitionGraph
      target.main.stage.carrier target.main.stage.actors target.main.stage.order
      target.main.stage.top target.main.cutoff target.main.birth) :
    MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega run.code extended.code := by
  let fields : Fin 32 → ZFSet.{u} := Fin.cases run.indices (Fin.cases run.stageGraph
    (Fin.cases run.transitionGraph (Fin.cases extended.stageGraph (Fin.cases extended.transitionGraph
      (Fin.cases target.code (Fin.cases target.main.birth (Fin.cases extended.indices target.rawFields)))))))
  have ground : ∀ j, fields j ∈ M.sets := Fin.cases run.indices_ground (Fin.cases run.stages_ground
    (Fin.cases run.transitions_ground (Fin.cases extended.stages_ground (Fin.cases extended.transitions_ground
      (Fin.cases (target.code_ground pairing) (Fin.cases target.main.birth_ground
        (Fin.cases extended.indices_ground (target.rawFields_ground pairing))))))))
  have targetFields : mainPrefixLimitTargetFields fields = target.rawFields := by
    funext j
    have same : Fin.natAdd 8 j = j.succ.succ.succ.succ.succ.succ.succ.succ := by
      apply Fin.ext
      change 8 + j.val = j.val + 8
      exact Nat.add_comm 8 j.val
    change fields (Fin.natAdd 8 j) = target.rawFields j
    rw [same]
    rfl
  refine ⟨fields, ground, ?_⟩
  unfold MainPrefixLimitStepRawCode
  rw [targetFields]
  exact ⟨indices, rfl, rfl, extension, entry, target.rawFields_code,
    target.rawFields_birth_entry, coverage⟩

theorem exists_limitStepCode (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indexMember : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ next ∈ M.sets,
      next ∈ level.recursionPrefixes
        (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD ∧
      MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega run.code next := by
  obtain ⟨data, chronology, target, extended, _, _, _, _, coverage, _, _, profiles,
      _, _, _, _, indices, indexMember', ground, rank, _, _, _, _, stageGraph,
      stageRestriction, transitionRestriction, _⟩ :=
    run.exists_rawCoveredPreservedAppendLimit preserved i₀ collection infinite choice columns_eq
      indexMember oldRank hK standard level
  have extension : MainPrefixExtends run.code extended.code := by
    apply (mainPrefixExtends_iff_restrictions run.graph_code extended.graph_code).2
    refine ⟨?_, stageRestriction, transitionRestriction⟩
    intro x hx
    rw [indices]
    exact ZFSet.mem_insert_iff.2 (Or.inr hx)
  have entry : ZFSet.pair run.indices target.code ∈ extended.stageGraph := by
    rw [stageGraph]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)
  have nonempty : extended.indices ≠ ∅ := by
    rw [indices]
    exact setSuccessor_ne_empty run.indices
  exact ⟨extended.code, ground,
    level.prefix_mem_recursionPrefixes extended profiles rank indexMember' nonempty,
    run.limitStepCode_of_fields target extended indices extension entry coverage⟩

end GroundMainPrefix

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (level : GroundMainCandidateLevel M K)

theorem exists_limitStepCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    {Labels C D rD old : ZFSet.{u}}
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (member : old ∈ level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD) :
    ∃ next ∈ M.sets,
      next ∈ level.recursionPrefixes
        (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD ∧
      MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega old next := by
  obtain ⟨T, _, indexMember, _, inhabited, ordinal, decoded⟩ :=
    level.exists_prefix_of_mem_recursionPrefixes pairing unions powers separation member
  let := ordinalMainIndexPreorder ordinal
  obtain ⟨run, indices, equal, preserved, rank⟩ := decoded
  obtain ⟨i₀⟩ := inhabited
  obtain ⟨next, ground, nextMember, step⟩ := run.exists_limitStepCode preserved i₀
    collection infinite choice columns_eq (indices.symm ▸ indexMember) rank hK standard level
  exact ⟨next, ground, nextMember, equal ▸ step⟩

end GroundMainCandidateLevel

end PartitionPilot.Forcing

end OAI
