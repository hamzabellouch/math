import OAI.SetTheory.PartitionPrinciple.Geometry.TaggedGrowthLayerRanks
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem time_rank_le_code : ZFSet.rank T ≤ ZFSet.rank fields.code :=
  rank_nonemptyTupleCode_field_le 6 fields.codeFields 0

theorem bound_rank_le_code : ZFSet.rank fields.bound ≤ ZFSet.rank fields.code :=
  rank_nonemptyTupleCode_field_le 6 fields.codeFields 1

theorem graph_rank_le_code (j : Fin 5) : ZFSet.rank (fields.graph j) ≤ ZFSet.rank fields.code :=
  rank_nonemptyTupleCode_field_le 6 fields.codeFields j.succ.succ

theorem value_rank_lt_code (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.rank (fields.value j s) < ZFSet.rank fields.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion (fields.value_entry j hs))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans (fields.graph_rank_le_code j))

end GroundChronologyFields

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

theorem fieldsCode_rank_le_code : ZFSet.rank serial.fields.code ≤ ZFSet.rank serial.code :=
  rank_nonemptyTupleCode_field_le 2 serial.codeFields 0

theorem time_rank_le_code : ZFSet.rank T ≤ ZFSet.rank serial.code :=
  serial.fields.time_rank_le_code.trans serial.fieldsCode_rank_le_code

theorem fieldGraph_rank_le_code (j : Fin 5) :
    ZFSet.rank (serial.fields.graph j) ≤ ZFSet.rank serial.code :=
  (serial.fields.graph_rank_le_code j).trans serial.fieldsCode_rank_le_code

theorem fieldValue_rank_lt_code (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.rank (serial.fields.value j s) < ZFSet.rank serial.code :=
  (serial.fields.value_rank_lt_code j hs).trans_le serial.fieldsCode_rank_le_code

theorem layerBound_rank_le_code : ZFSet.rank serial.layerBound ≤ ZFSet.rank serial.code :=
  rank_nonemptyTupleCode_field_le 2 serial.codeFields 1

theorem layers_rank_le_code : ZFSet.rank serial.layers ≤ ZFSet.rank serial.code :=
  rank_nonemptyTupleCode_field_le 2 serial.codeFields 2

theorem layerWitness_rank_lt_code {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    ZFSet.rank (serial.layerWitness s t) < ZFSet.rank serial.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion (serial.layerWitness_entry hs ht earlier))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans serial.layers_rank_le_code)

end GroundSerializedChronology
end PartitionPilot.Forcing

end

end OAI
