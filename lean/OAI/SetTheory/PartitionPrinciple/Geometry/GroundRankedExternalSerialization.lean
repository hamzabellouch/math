import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRankedSerializedChronology

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "comp" => certificate.compression
local notation "completion" => certificate.compression.born.profiled.heighted.completion
local notation "births" => certificate.births
local notation "heights" => certificate.heights
local notation "external" => certificate.external

theorem exists_rankedExternalSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
    (original : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (originalRank : ZFSet.rank original.code < ZFSet.rank K)
    (originalAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      original.fields.value j s = source.history.fieldValue j s)
    (prior : GroundSerializedChronology M (insert (comp).born.births.limit (comp).born.births.limit) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert (comp).born.births.limit (comp).born.births.limit →
      prior.fields.value j s = (comp).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).history.fieldValue j s) ∧
      serial.layerBound = functionGraphRange
        (chronologyPairs (insert (births).limit (births).limit)) serial.layers := by
  have atBase (j : Fin 5) := agreement j (comp).born.births.limit (ZFSet.mem_insert _ _)
  have sourceValues := (comp).limit_values
  have sourceMatch : prior.fields.value 0 (comp).born.births.limit = (completion).algebra.union.fields 0 ∧
      prior.fields.value 1 (comp).born.births.limit = (completion).algebra.union.fields 1 ∧
      prior.fields.value 2 (comp).born.births.limit = (completion).algebra.union.fields 2 ∧
      prior.fields.value 3 (comp).born.births.limit = (comp).born.births.birth :=
    ⟨(atBase 0).trans sourceValues.1, (atBase 1).trans sourceValues.2.1,
      (atBase 2).trans sourceValues.2.2.1, (atBase 3).trans sourceValues.2.2.2.1⟩
  let fields := (births).serializedFields heights prior (external).inputs
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _)
  have values : ∀ j s, s ∈ insert (births).limit (births).limit →
      fields.value j s = (external).history.fieldValue j s := by
    intro j s hs
    rw [(births).serializedFields_value heights prior (external).inputs
      source.stage.group_code source.stage.action_code pairing unions powers separation infinite
      source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _) j hs]
    have oldValue (a : ZFSet.{u}) (before : a ∈ (comp).born.births.limit ∨ a = (comp).born.births.limit) :
        ((births).chronologyFields heights prior.toHistory).fieldValue j a = (external).history.fieldValue j a := by
      have ha : a ∈ insert (comp).born.births.limit (comp).born.births.limit := before.elim
        (fun h => ZFSet.mem_insert_of_mem _ h) (fun h => h.symm ▸ ZFSet.mem_insert _ _)
      have left := (births).chronologyFields_old heights prior.toHistory before
      have right := (external).old_values a before
      have eLeft : ((births).chronologyFields heights prior.toHistory).fieldValue j a = prior.fields.value j a :=
        Fin.cases left.1 (Fin.cases left.2.1 (Fin.cases left.2.2.1
          (Fin.cases left.2.2.2.1 (Fin.cases left.2.2.2.2 (fun i => Fin.elim0 i))))) j
      have eRight : (external).history.fieldValue j a = (comp).history.fieldValue j a :=
        Fin.cases right.1 (Fin.cases right.2.1 (Fin.cases right.2.2.1
          (Fin.cases right.2.2.2.1 (Fin.cases right.2.2.2.2 (fun i => Fin.elim0 i))))) j
      exact eLeft.trans ((agreement j a ha).trans eRight.symm)
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · have left := (births).chronologyFields_limit heights prior.toHistory
      have right := (external).limit_values
      exact Fin.cases (left.1.trans right.1.symm)
        (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
          (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
            (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
    · rcases ((births).times.mem_limit_iff s).1 hs with before | equal | ⟨n, rfl⟩
      · exact oldValue s (Or.inl before)
      · exact oldValue s (Or.inr equal)
      · have left := (births).chronologyFields_stamp heights prior.toHistory n
        have right := (external).stamp_values n
        exact Fin.cases (left.1.trans right.1.symm)
          (Fin.cases (left.2.1.trans right.2.1.symm) (Fin.cases (left.2.2.1.trans right.2.2.1.symm)
            (Fin.cases (left.2.2.2.1.trans right.2.2.2.1.symm)
              (Fin.cases (left.2.2.2.2.trans right.2.2.2.2.symm) (fun i => Fin.elim0 i))))) j
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks : ZFSet.rank (source.stage.compressionTasks Labels) < ZFSet.rank K :=
    M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order source.stage.meetGraph
      source.stage.action invariant.points_rank invariant.labels_rank
  have graphs := certificate.externalFieldGraphs_rank_lt pairing unions powers separation collection
    infinite hK conditions invariant original originalRank originalAgreement fields values
  have raw := (births).serialized_all_ranked_raw_witnesses heights prior (external).inputs
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (ZFSet.mem_insert _ _)
    priorRank sourceMatch limit (ZFSet.rank_lt_of_mem conditions.2.1)
    tasks invariant.points_rank invariant.actors_rank
  have times := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  obtain ⟨serial, ground, rank, member, _, exactValues, exactRange⟩ :=
    fields.exists_rankedSerialization pairing unions powers separation collection infinite choice
      hK conditions times level (ordinalSetProperty_succ (births).times.ordinal)
      ((births).serializedFields_core heights prior (external).inputs source.stage.group_code source.stage.action_code
        pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
        (ZFSet.mem_insert _ _)) graphs raw
  exact ⟨serial, ground, rank, member, fun j s hs => (exactValues j s).trans (values j s hs), exactRange⟩

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
