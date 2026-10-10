import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRankedLayerSelection
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSerializedBoundNormalization
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSerializedCandidateLevels

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD K : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem exists_rankedSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (level : GroundMainCandidateLevel M K)
    (ordinal : ordinalSetProperty T)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (graphs : ∀ j, ZFSet.rank (fields.graph j) < ZFSet.rank K)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < ZFSet.rank K ∧
        GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
          (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ serial : GroundSerializedChronology M T C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧
        serial.fields.graph = fields.graph ∧
        (∀ j s, serial.fields.value j s = fields.value j s) ∧
        serial.layerBound = functionGraphRange (chronologyPairs T) serial.layers := by
  obtain ⟨layers, hLayers, function, layerRank, codes⟩ :=
    fields.choose_rankedLayerGraph pairing unions powers separation collection infinite choice
      hK conditions hT level.carrier_ground level.membership core rawWitnesses
  let selected : GroundSerializedChronology M T C D rD :=
    ⟨fields, ordinal, core, level.carrier, level.carrier_ground, layers, hLayers, function, codes⟩
  let serial := selected.normalizeBounds pairing unions powers separation
  have rank : ZFSet.rank serial.code < ZFSet.rank K :=
    selected.normalizeBounds_code_rank_lt pairing unions powers separation
      (conditions.rank_isLimit pairing unions powers separation infinite hK)
      (ZFSet.rank_lt_of_mem hT) graphs layerRank
  exact ⟨serial, serial.code_ground pairing, rank,
    level.ranked_mem_validChronologies pairing serial rank, rfl, fun _ _ => rfl, rfl⟩

end PartitionPilot.Forcing.GroundChronologyFields

end

end OAI
