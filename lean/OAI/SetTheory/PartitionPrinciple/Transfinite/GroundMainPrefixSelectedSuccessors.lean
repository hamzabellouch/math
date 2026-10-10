import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialPreservedMainPrefix

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_rankedAppendSelected
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (last : I) (greatest : ∀ i, i ≤ last) (preserved : run.PreservesOldProfiles)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hLabels : Labels ∈ M.sets)
    (level : GroundMainCandidateLevel M K) {f targetCode z : ZFSet.{u}}
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD)
    (entry : ZFSet.pair (run.linked last).code (ZFSet.pair targetCode z) ∈ f) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      ∃ step : GroundChronologicalMainTransition (run.diagram.stage last) target.main,
        ∃ covered : step.CoversOldBirths,
          ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
            extended = run.appendLast last greatest target step covered ∧
            extended.PreservesOldProfiles ∧
            target.code = targetCode ∧ step.map.code = z ∧ step.PreservesOldProfiles ∧
            extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
            extended.code ∈ level.validMainPrefixes Labels C D rD ∧
            extended.indices = insert run.indices run.indices ∧
            (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
            extended.linked ⊤ = target ∧
            extended.stageGraph = insert (ZFSet.pair run.indices targetCode) run.stageGraph ∧
            graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
            graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
            (∀ (i j : I) (before : i ≤ j),
              (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
                (run.diagram.transition before).map.code) ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.points = step.map.points ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.actors = step.map.actors ∧
            TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
              (run.linked last).code (extended.linked ⊤).code
              (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code := by
  have hC := (run.linked last).main.stage.columns_ground
  have hD := (run.linked last).main.stage.coordinates_ground
  have hrD := (run.linked last).main.stage.coordinate_order_ground
  have hS := M.linkedMainStageCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD standard.1.1
  have subset : M.linkedMainStageCandidates level.carrier K Labels C D rD ⊆ level.carrier := by
    intro x hx
    exact ((M.mem_linkedMainStageCandidates level.carrier K Labels C D rD x).1 hx).1
  obtain ⟨_, targetMember, _, code⟩ :=
    (M.taskBearingSuccessorRelation_entry pairing unions powers separation collection infinite
      hS level.carrier_ground hK hLabels hC hD hrD standard.1.1 subset
      (run.linked last).code targetCode z).1 (selected entry)
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨target, step, covered, extended, equal, targetEqual, mapEqual, stepPreserved, rest⟩ :=
    run.exists_rankedAppendTaskBearing last greatest oldRank
      (conditions.rank_isLimit pairing unions powers separation infinite hK) level
      ((level.membership targetCode).1 (subset targetMember)).2 code
  refine ⟨target, step, covered, extended, equal, ?_, targetEqual, mapEqual, stepPreserved, rest⟩
  rw [equal]
  exact run.appendLast_preservesOldProfiles preserved last greatest target step covered stepPreserved

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
