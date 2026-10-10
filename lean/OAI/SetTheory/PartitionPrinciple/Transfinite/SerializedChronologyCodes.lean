import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def ChronologyLayerEntries (T N : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (layers : ZFSet.{u}) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ L r μ birth z,
    ZFSet.pair s L ∈ graphs 0 → ZFSet.pair s r ∈ graphs 1 →
    ZFSet.pair s μ ∈ graphs 2 → ZFSet.pair s birth ∈ graphs 3 →
    ZFSet.pair (ZFSet.pair s t) z ∈ layers →
      GrowthLayerWitnessCode (graphs 0) (graphs 1) (graphs 2) L r μ birth t N z

structure SerializedChronologyCode (T V C D rD N : ZFSet.{u})
    (graphs : Fin 5 → ZFSet.{u}) (W layers : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty T
  core : ChronologyCoreCode T V C D rD graphs
  function : ZFSet.IsFunc (chronologyPairs T) W layers
  entries : ChronologyLayerEntries T N graphs layers

namespace ChronologyCoreCode
theorem meet_of_entries {T V C D rD s L r μ birth : ZFSet.{u}}
    {graphs : Fin 5 → ZFSet.{u}} (core : ChronologyCoreCode T V C D rD graphs)
    (hs : s ∈ T) (eL : ZFSet.pair s L ∈ graphs 0) (er : ZFSet.pair s r ∈ graphs 1)
    (eμ : ZFSet.pair s μ ∈ graphs 2) (eb : ZFSet.pair s birth ∈ graphs 3) :
    MeetOrderCode L r μ := by
  obtain ⟨height, entry, _⟩ := (core.function 4).2 s hs
  exact (core.point s hs L r μ birth height eL er eμ eb entry).meet
end ChronologyCoreCode

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}

theorem raw_code (serial : GroundSerializedChronology M T C D rD) :
    SerializedChronologyCode T serial.fields.bound C D rD ZFSet.omega
      serial.fields.graph serial.layerBound serial.layers := by
  refine ⟨serial.ordinal, serial.core, serial.layer_function, ?_⟩
  intro s hs t ht earlier L r μ birth z eL er eμ eb entry
  have code := serial.layer_code s hs t ht earlier z entry
  rw [serial.fields.value_eq_of_entry 0 eL, serial.fields.value_eq_of_entry 1 er,
    serial.fields.value_eq_of_entry 2 eμ, serial.fields.value_eq_of_entry 3 eb] at code
  exact code
end GroundSerializedChronology

namespace SerializedChronologyCode
variable {M : TransitiveGround.{u}} {T V C D rD N W layers : ZFSet.{u}}
variable {graphs : Fin 5 → ZFSet.{u}}

noncomputable def toGround (code : SerializedChronologyCode T V C D rD N graphs W layers)
    (hT : T ∈ M.sets) (hV : V ∈ M.sets) (hGraphs : ∀ j, graphs j ∈ M.sets)
    (hW : W ∈ M.sets) (hLayers : layers ∈ M.sets) (omega : N = ZFSet.omega) :
    GroundSerializedChronology M T C D rD where
  fields := ⟨hT, V, hV, graphs, hGraphs, code.core.function⟩
  ordinal := code.ordinal
  core := code.core
  layerBound := W
  layer_bound_ground := hW
  layers := layers
  layers_ground := hLayers
  layer_function := code.function
  layer_code := by
    intro s hs t ht earlier z entry
    let fields : GroundChronologyFields M T := ⟨hT, V, hV, graphs, hGraphs, code.core.function⟩
    exact omega ▸ code.entries s hs t ht earlier _ _ _ _ z
      (fields.value_entry 0 hs) (fields.value_entry 1 hs)
      (fields.value_entry 2 hs) (fields.value_entry 3 hs) entry

theorem toGround_fields (code : SerializedChronologyCode T V C D rD N graphs W layers)
    (hT : T ∈ M.sets) (hV : V ∈ M.sets) (hGraphs : ∀ j, graphs j ∈ M.sets)
    (hW : W ∈ M.sets) (hLayers : layers ∈ M.sets) (omega : N = ZFSet.omega) :
    let serial := code.toGround hT hV hGraphs hW hLayers omega
    serial.fields.bound = V ∧ serial.fields.graph = graphs ∧
      serial.layerBound = W ∧ serial.layers = layers := ⟨rfl, rfl, rfl, rfl⟩
end SerializedChronologyCode

end PartitionPilot.Forcing

end

end OAI
