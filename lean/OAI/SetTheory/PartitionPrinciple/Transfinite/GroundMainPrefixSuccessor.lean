import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialPreservedMainPrefix

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_rankedAppendLast {K Labels D rD c : ZFSet.{u}}
    {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (last : I) (greatest : ∀ i, i ≤ last)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (level : GroundMainCandidateLevel M K) :
    ∃ certificate : GroundInitialMainSuccessorData M C D rD (run.linked last).main Labels,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          target.main = certificate.target ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.diagram.stage ⊤ = certificate.target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code =
            certificate.transition.map.code ∧
          (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.points =
            certificate.transition.map.points ∧
          (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.actors =
            certificate.transition.map.actors := by
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice (run.linked last).main hLabels hc dense above coordinateInjection
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨serial, _serialGround, serialRank, serialMember, agreement, _terminal⟩ :=
    certificate.exists_rankedTargetSerialization pairing unions powers separation collection infinite choice
      hK conditions (run.linked last).invariant level (run.linked last).serial
      (run.linked last).serial_rank (run.linked last).agreement
  let target : GroundLinkedMainStage M K Labels C D rD :=
    ⟨certificate.target, serial, agreement,
      certificate.target_invariant pairing unions powers separation collection infinite choice
        hLabels hK standard (run.linked last).invariant, serialRank⟩
  let step : GroundChronologicalMainTransition (run.diagram.stage last) target.main :=
    certificate.transition.retargetEq (run.linked_main last) rfl
  have covered : step.CoversOldBirths :=
    (certificate.transition.retargetEq_coversOldBirths_iff (run.linked_main last) rfl).2
      certificate.coversOldBirths
  let extended := run.appendLast last greatest target step covered
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendLast_code_rank_lt last greatest target step covered
      (conditions.rank_isLimit pairing unions powers separation infinite hK) oldRank
      (target.code_rank_lt pairing unions powers separation infinite hK conditions)
  refine ⟨certificate, target, extended, rfl, serialMember,
    run.appendLast_indices last greatest target step covered, extended.code_ground, rank,
    level.prefix_mem_validMainPrefixes extended rank,
    run.appendLast_linked_old last greatest target step covered,
    run.appendLast_linked_top last greatest target step covered, rfl,
    run.appendLast_stageGraph last greatest target step covered,
    run.appendLast_stageGraph_restrict last greatest target step covered,
    run.appendLast_transitionGraph_restrict last greatest target step covered, ?_, ?_, ?_, ?_⟩
  · intro i j before
    rfl
  · rw [run.appendLast_transition_last last greatest target step covered]
    exact certificate.transition.retargetEq_code (run.linked_main last) rfl
  · rw [run.appendLast_transition_last last greatest target step covered]
    exact certificate.transition.retargetEq_points (run.linked_main last) rfl
  · rw [run.appendLast_transition_last last greatest target step covered]
    exact certificate.transition.retargetEq_actors (run.linked_main last) rfl

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
