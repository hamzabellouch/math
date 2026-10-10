import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRankedSerializedChronology

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression

theorem exists_rankedCompressionSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
        serial.fields.value j s = (comp).history.fieldValue j s) ∧
      serial.layerBound = functionGraphRange
        (chronologyPairs (insert (comp).born.births.limit (comp).born.births.limit)) serial.layers := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks : ZFSet.rank (source.stage.compressionTasks Labels) < ZFSet.rank K :=
    M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order
      source.stage.meetGraph source.stage.action invariant.points_rank invariant.labels_rank
  obtain ⟨fields, _, core, values, raw⟩ := certificate.origin.exists_rankedRawCompressionFields comp prior
    pairing unions powers separation collection infinite
    certificate.indices_ground certificate.sources_ground certificate.representatives_ground
    source.stage.actors_ground certificate.task_action_ground (ZFSet.mem_insert _ _)
    limit priorRank tasks tasks
    (M.initialCompressionData_template_constancy source.stage.carrier source.stage.actors
      source.stage.order source.stage.meetGraph source.stage.action Labels)
    rfl rfl rfl source.carrier_eq source.order_eq source.meet_eq rfl agreement
  have graphs := certificate.compressionFieldGraphs_rank_lt pairing unions powers separation
    collection infinite hK conditions invariant prior priorRank agreement fields values
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  obtain ⟨serial, ground, rank, member, _, exactValues, exactRange⟩ :=
    fields.exists_rankedSerialization pairing unions powers separation collection infinite choice
      hK conditions times level (ordinalSetProperty_succ (comp).born.births.times.ordinal) core graphs raw
  exact ⟨serial, ground, rank, member, fun j s hs => (exactValues j s).trans (values j s hs), exactRange⟩

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
