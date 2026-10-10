import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRankedFixedTopSerialization

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
local notation "births" => certificate.births
local notation "heights" => certificate.heights
local notation "external" => certificate.external
include pairing unions powers separation collection infinite choice hK conditions invariant

theorem exists_rankedBoundedSerialization
    (prior : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert (births).limit (births).limit →
      prior.fields.value j s = (external).history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert (births).limit (births).limit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧ ∀ j s, s ∈ insert (births).limit (births).limit →
        serial.fields.value j s = (external).bounded_history.fieldValue j s := by
  have space := (agreement 0 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.1
  have order := (agreement 1 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.1
  have birth := (agreement 3 (births).limit (ZFSet.mem_insert _ _)).trans (external).limit_values.2.2.2.1
  have earlier : ∀ x t, ZFSet.pair x t ∈ prior.fields.value 3 (births).limit → t ∈ (births).limit := by
    intro x t entry
    rw [birth] at entry
    exact (ZFSet.pair_mem_prod.1 ((births).function.1 entry)).2
  have heightCode : StrictLexHeightCode (fixedTopCarrier (prior.fields.value 0 (births).limit)) C D
      (fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit))
      (heights).boundedHeight rD := by
    rw [space, order]
    exact certificate.boundedHeights.code
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have time := conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.external_limit_mem pairing unions powers separation infinite hK conditions invariant.cutoff_mem)
  have points := (certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions invariant.points_rank invariant.labels_rank invariant.actors_rank).1
  rw [certificate.target_fields.1] at points
  have heightRank := SetRealization.rank_functionGraph_lt limit certificate.boundedHeights.code.function
    points (SetRealization.rank_product_lt limit invariant.columns_rank invariant.coordinates_rank)
  obtain ⟨serial, ground, rank, member, _, values⟩ := prior.exists_rankedFixedTopSerialization
    pairing unions powers separation collection infinite choice hK conditions time level priorRank
    (heights).boundedHeight certificate.boundedHeights.height_ground heightRank
    (births).times.ordinal earlier heightCode
  have terminal (j : Fin 5) : prior.fixedTopValues (heights).boundedHeight j =
      (external).bounded_history.fieldValue j (births).limit := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) j
    · change fixedTopCarrier (prior.fields.value 0 (births).limit) = _
      rw [space]
      exact (external).bounded_values.1.symm
    · change fixedTopOrder (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.1.symm
    · change fixedTopMeet (prior.fields.value 0 (births).limit) (prior.fields.value 1 (births).limit) = _
      rw [space, order]
      exact (external).bounded_values.2.2.1.symm
    · change fixedTopBirth (prior.fields.value 0 (births).limit) (prior.fields.value 3 (births).limit) (births).limit = _
      rw [space, birth]
      exact (external).bounded_values.2.2.2.1.symm
    · exact (external).bounded_values.2.2.2.2.symm
  refine ⟨serial, ground, rank, member, ?_⟩
  intro j s hs
  rw [values j s hs]
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [appendHistoryValue_at]
    exact terminal j
  · rw [appendHistoryValue_old hs]
    have previous := (external).bounded_old_values s hs
    have same : (external).bounded_history.fieldValue j s = (external).history.fieldValue j s :=
      Fin.cases previous.1 (Fin.cases previous.2.1 (Fin.cases previous.2.2.1
        (Fin.cases previous.2.2.2.1 (Fin.cases previous.2.2.2.2 (fun i => Fin.elim0 i))))) j
    exact (agreement j s (ZFSet.mem_insert_of_mem _ hs)).trans same.symm

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

end OAI
