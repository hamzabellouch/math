import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)

noncomputable def normalizeBounds : GroundSerializedChronology M T C D rD where
  fields := serial.fields.normalizeBound pairing unions separation
  ordinal := serial.ordinal
  core := serial.fields.normalizeBound_core pairing unions separation serial.core
  layerBound := functionGraphRange (chronologyPairs T) serial.layers
  layer_bound_ground := M.functionGraphRange_mem unions separation
    (M.chronologyPairs_mem pairing unions powers separation serial.fields.time_ground)
    serial.layers_ground
  layers := serial.layers
  layers_ground := serial.layers_ground
  layer_function := functionGraphRange_function ⟨serial.layerBound, serial.layer_function⟩
  layer_code := serial.layer_code

theorem normalizeBounds_graph :
    (serial.normalizeBounds pairing unions powers separation).fields.graph = serial.fields.graph := rfl

theorem normalizeBounds_value (j : Fin 5) (s : ZFSet.{u}) :
    (serial.normalizeBounds pairing unions powers separation).fields.value j s =
      serial.fields.value j s := rfl

theorem normalizeBounds_layers :
    (serial.normalizeBounds pairing unions powers separation).layers = serial.layers := rfl

theorem normalizeBounds_layerWitness (s t : ZFSet.{u}) :
    (serial.normalizeBounds pairing unions powers separation).layerWitness s t =
      serial.layerWitness s t := rfl

theorem normalizeBounds_toHistory :
    (serial.normalizeBounds pairing unions powers separation).toHistory = serial.toHistory := rfl

theorem normalizeBounds_code_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (time : ZFSet.rank T < o) (graphs : ∀ j, ZFSet.rank (serial.fields.graph j) < o)
    (layers : ZFSet.rank serial.layers < o) :
    ZFSet.rank (serial.normalizeBounds pairing unions powers separation).code < o :=
  rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (serial.fields.normalizeBound_code_rank_lt pairing unions separation limit time graphs)
      (Fin.cases ((functionGraphRange_rank_le (chronologyPairs T) serial.layers).trans_lt layers)
        (fun _ => layers)))

end PartitionPilot.Forcing.GroundSerializedChronology

end

end OAI
