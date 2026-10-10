import OAI.SetTheory.PartitionPrinciple.Forcing.GrowthLayerWitnessRestrictions
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T S C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hS : S ∈ M.sets) (subset : S ⊆ T) (ordinal : ordinalSetProperty S)

noncomputable def restrictTo : GroundSerializedChronology M S C D rD where
  fields := serial.fields.restrictTo unions separation hS subset
  ordinal := ordinal
  core := serial.fields.restrictTo_core unions separation hS subset serial.core ordinal.1
  layerBound := serial.layerBound
  layer_bound_ground := serial.layer_bound_ground
  layers := graphRestriction (chronologyPairs S) serial.layers
  layers_ground := M.graphRestriction_mem unions separation
    (M.chronologyPairs_mem pairing unions powers separation hS) serial.layers_ground
  layer_function := by
    let function : FunctionGraphOn (chronologyPairs T) serial.layers :=
      ⟨serial.layerBound, serial.layer_function⟩
    refine ⟨?_, (function.restrict (chronologyPairs_mono subset)).to_isFunc.2⟩
    intro z hz
    obtain ⟨p, hp, w, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hp, (ZFSet.pair_mem_prod.1 (serial.layer_function.1 entry)).2⟩
  layer_code := by
    intro s hs t ht earlier z entry
    change GrowthLayerWitnessCode (graphRestriction S (serial.fields.graph 0))
      (graphRestriction S (serial.fields.graph 1)) (graphRestriction S (serial.fields.graph 2))
      ((serial.fields.restrictTo unions separation hS subset).value 0 s)
      ((serial.fields.restrictTo unions separation hS subset).value 1 s)
      ((serial.fields.restrictTo unions separation hS subset).value 2 s)
      ((serial.fields.restrictTo unions separation hS subset).value 3 s) t ZFSet.omega z
    rw [serial.fields.restrictTo_value unions separation hS subset 0 hs,
      serial.fields.restrictTo_value unions separation hS subset 1 hs,
      serial.fields.restrictTo_value unions separation hS subset 2 hs,
      serial.fields.restrictTo_value unions separation hS subset 3 hs]
    exact (serial.layer_code s (subset hs) t (subset ht) earlier z
      (pair_mem_graphRestriction.1 entry).1).restrict_sources ordinal.1 ht

theorem restrictTo_graph (j : Fin 5) :
    (serial.restrictTo pairing unions powers separation hS subset ordinal).fields.graph j =
      graphRestriction S (serial.fields.graph j) := rfl

theorem restrictTo_layers :
    (serial.restrictTo pairing unions powers separation hS subset ordinal).layers =
      graphRestriction (chronologyPairs S) serial.layers := rfl

theorem restrictTo_value (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ S) :
    (serial.restrictTo pairing unions powers separation hS subset ordinal).fields.value j s =
      serial.fields.value j s :=
  serial.fields.restrictTo_value unions separation hS subset j hs

theorem restrictTo_layerWitness {s t : ZFSet.{u}} (hs : s ∈ S) (ht : t ∈ S)
    (earlier : t = s ∨ t ∈ s) :
    (serial.restrictTo pairing unions powers separation hS subset ordinal).layerWitness s t =
      serial.layerWitness s t := by
  have entry := (serial.restrictTo pairing unions powers separation hS subset ordinal).layerWitness_entry
    hs ht earlier
  exact ((show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue_eq_of_entry
      (pair_mem_graphRestriction.1 entry).1).symm

theorem restrictTo_history_values {s : ZFSet.{u}} (hs : s ∈ S) :
    let restricted := serial.restrictTo pairing unions powers separation hS subset ordinal
    restricted.toHistory.space s = serial.toHistory.space s ∧
      restricted.toHistory.order s = serial.toHistory.order s ∧
      restricted.toHistory.meetGraph s = serial.toHistory.meetGraph s ∧
      restricted.toHistory.birth s = serial.toHistory.birth s ∧
      restricted.toHistory.height s = serial.toHistory.height s :=
  ⟨serial.restrictTo_value pairing unions powers separation hS subset ordinal 0 hs,
    serial.restrictTo_value pairing unions powers separation hS subset ordinal 1 hs,
    serial.restrictTo_value pairing unions powers separation hS subset ordinal 2 hs,
    serial.restrictTo_value pairing unions powers separation hS subset ordinal 3 hs,
    serial.restrictTo_value pairing unions powers separation hS subset ordinal 4 hs⟩

theorem restrictTo_code_ground :
    (serial.restrictTo pairing unions powers separation hS subset ordinal).code ∈ M.sets :=
  (serial.restrictTo pairing unions powers separation hS subset ordinal).code_ground pairing

end PartitionPilot.Forcing.GroundSerializedChronology

end

end OAI
