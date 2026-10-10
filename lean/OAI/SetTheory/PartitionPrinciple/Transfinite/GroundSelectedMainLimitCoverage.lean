import OAI.SetTheory.PartitionPrinciple.Forcing.MainPrefixConditionalStepCodes

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v w
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {J : Type w} [Small.{u} J] [Preorder J]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (next : GroundMainPrefix M K Labels C D rD pairing unions powers separation J)

theorem exists_extensionCone (extension : MainPrefixExtends run.code next.code)
    (indices : next.indices = insert run.indices run.indices) :
    ∃ j : J, next.key j = run.indices ∧
      ∃ cone : run.diagram.Cone (next.diagram.stage j),
        (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ next.transitionGraph ↔
          z = (cone.leg i).map.code) ∧
        ∀ i, (cone.leg i).CoversOldBirths := by
  classical
  have included : run.indices ⊆ next.indices ∧ run.stageGraph ⊆ next.stageGraph ∧
      run.transitionGraph ⊆ next.transitionGraph := mainPrefixExtends_iff.1 extension
  have topMember : run.indices ∈ next.indices := by
    rw [indices]
    exact ZFSet.mem_insert _ _
  obtain ⟨j, key⟩ := ZFSet.mem_range.1 topMember
  have targetEntry : ZFSet.pair run.indices (next.linked j).code ∈ next.stageGraph := by
    rw [← key]
    exact (next.stageGraph_entry j _).2 rfl
  have legs (i : I) :
      ∃ step : GroundChronologicalMainTransition (run.diagram.stage i) (next.diagram.stage j),
        ZFSet.pair (ZFSet.pair run.indices (run.key i)) step.map.code ∈ next.transitionGraph ∧
        step.CoversOldBirths := by
    have oldMember : run.key i ∈ run.indices := ZFSet.mem_range.2 ⟨i, rfl⟩
    have pairMember : ZFSet.pair run.indices (run.key i) ∈ chronologyPairs next.indices :=
      (pair_mem_chronologyPairs _ _ _).2 ⟨topMember, included.1 oldMember, Or.inr oldMember⟩
    obtain ⟨z, entry⟩ := next.transitionGraph_function.total pairMember
    have valid := next.graph_code.transition_valid (run.key i) run.indices
      (run.linked i).code (next.linked j).code z
      (included.2.1 ((run.stageGraph_entry i _).2 rfl)) targetEntry entry
    obtain ⟨step, code, covered⟩ := valid.exists_at (run.linked i) (next.linked j)
    let actual := step.retargetEq (run.linked_main i) (next.linked_main j)
    refine ⟨actual, ?_, (step.retargetEq_coversOldBirths_iff
      (run.linked_main i) (next.linked_main j)).2 covered⟩
    simpa only [actual, GroundChronologicalMainTransition.retargetEq_code, code] using entry
  let leg := fun i => Classical.choose (legs i)
  have entry (i : I) :
      ZFSet.pair (ZFSet.pair run.indices (run.key i)) (leg i).map.code ∈ next.transitionGraph :=
    (Classical.choose_spec (legs i)).1
  have coherent : ∀ {i k : I} (before : i ≤ k),
      (run.diagram.transition before).comp pairing unions powers separation (leg k) = leg i := by
    intro i k before
    have composition := next.graph_code.composition (run.key i) (run.key k) run.indices
      _ _ _ _ _ _ (included.2.2 ((run.transitionGraph_entry before _).2 rfl)) (entry k) (entry i)
    apply GroundChronologicalMainTransition.ext
    apply GroundMainTransition.ext
    · exact (composition.1.eq_relationCompose
        (run.diagram.transition before).map.point_embedding.injection.function
        (leg i).map.point_embedding.injection.function.1).symm
    · exact (composition.2.eq_relationCompose
        (run.diagram.transition before).map.group_embedding.injection.function
        (leg i).map.group_embedding.injection.function.1).symm
  let cone : run.diagram.Cone (next.diagram.stage j) := ⟨leg, coherent⟩
  refine ⟨j, key, cone, ?_, fun i => (Classical.choose_spec (legs i)).2⟩
  intro i z
  exact ⟨fun given => next.transitionGraph_function.unique given (entry i),
    fun equal => equal.symm ▸ entry i⟩

theorem exists_limitCone_of_limitStep
    (code : MainPrefixLimitStepCode M K Labels C D rD ZFSet.omega run.code next.code) :
    ∃ j : J, next.key j = run.indices ∧
      ∃ cone : run.diagram.Cone (next.diagram.stage j),
        (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ next.transitionGraph ↔
          z = (cone.leg i).map.code) ∧
        (∀ i, (cone.leg i).CoversOldBirths) ∧
        run.LimitCoverage (next.diagram.stage j) cone := by
  have indices : next.indices = insert run.indices run.indices := code.indices_successor rfl rfl
  obtain ⟨j, key, cone, entries, covered⟩ := run.exists_extensionCone next code.extension indices
  obtain ⟨fields, _, successor, oldCode, nextCode, _, targetEntry, linked, birthEntry, coverage⟩ := code
  have oldFields := mainPrefixCode_inj.1 (show mainPrefixCode run.indices run.stageGraph run.transitionGraph =
    mainPrefixCode (fields 0) (fields 1) (fields 2) from oldCode)
  have nextFields := mainPrefixCode_inj.1 (show mainPrefixCode next.indices next.stageGraph next.transitionGraph =
    mainPrefixCode (fields 7) (fields 3) (fields 4) from nextCode)
  have actualTarget : ZFSet.pair run.indices (fields 5) ∈ next.stageGraph := by
    simpa only [← oldFields.1, ← nextFields.2.1] using targetEntry
  have knownTarget : ZFSet.pair run.indices (next.linked j).code ∈ next.stageGraph := by
    rw [← key]
    exact (next.stageGraph_entry j _).2 rfl
  have targetCode := next.stageGraph_function.unique actualTarget knownTarget
  have actualLinked : LinkedMainStageRawCode M K Labels C D rD ZFSet.omega
      (next.linked j).code (mainPrefixLimitTargetFields fields) := targetCode ▸ linked
  have targetFields := actualLinked.fields_unique (next.linked j).rawFields_code
  rw [targetFields] at birthEntry coverage
  have birthEqual : fields 6 = (next.linked j).main.birth :=
    ((next.linked j).serial.fields.graphFunction 3).unique birthEntry (next.linked j).rawFields_birth_entry
  have actualCoverage : MainLimitCoverageGraphCode run.indices run.stageGraph next.transitionGraph
      (next.diagram.stage j).stage.carrier (next.diagram.stage j).stage.actors
      (next.diagram.stage j).stage.order (next.diagram.stage j).stage.top
      (next.diagram.stage j).cutoff (next.diagram.stage j).birth := by
    change MainLimitCoverageGraphCode (fields 0) (fields 1) (fields 4)
      (next.linked j).main.stage.carrier (next.linked j).main.stage.actors
      (next.linked j).main.stage.order (next.linked j).main.stage.top
      (next.linked j).main.cutoff (fields 6) at coverage
    rw [← oldFields.1, ← oldFields.2.1, ← nextFields.2.2, birthEqual, next.linked_main j] at coverage
    exact coverage
  exact ⟨j, key, cone, entries, covered, (run.limitCoverage_graph_iff cone entries).1 actualCoverage⟩

theorem exists_limitCone_of_conditionalStep {f : ZFSet.{u}}
    (code : MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f run.code next.code)
    (nonzero : NonzeroLimitOrdinalCode run.indices) :
    ∃ j : J, next.key j = run.indices ∧
      ∃ cone : run.diagram.Cone (next.diagram.stage j),
        (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ next.transitionGraph ↔
          z = (cone.leg i).map.code) ∧
        (∀ i, (cone.leg i).CoversOldBirths) ∧
        run.LimitCoverage (next.diagram.stage j) cone :=
  run.exists_limitCone_of_limitStep next (code.limit_of_nonzeroLimit rfl nonzero)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
