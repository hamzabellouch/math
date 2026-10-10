import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRowTerms

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

theorem exists_rankedAppendLimit_of_indices_mem (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indices : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite ∧
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
  obtain ⟨data, target, extended, result⟩ := run.exists_rankedAppendLimit i₀ collection infinite choice
    columns_eq (M.groundOmegaOne_member_countable pairing unions powers separation collection infinite indices)
    oldRank hK standard level
  have index_eq := result.2.2.2.2.1
  refine ⟨data, target, extended, result.1, result.2.1, result.2.2.1, result.2.2.2.1,
    index_eq, ?_, result.2.2.2.2.2⟩
  rw [index_eq]
  exact M.groundOmegaOne_successor pairing unions powers separation collection infinite indices

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
