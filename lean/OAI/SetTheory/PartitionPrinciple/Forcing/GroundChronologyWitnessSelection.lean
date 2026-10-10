import OAI.SetTheory.PartitionPrinciple.Models.GroundOrdinalPartitionInjectionAssembly
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyLayerRelation

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
variable (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
  ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
    (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z)
include pairing unions powers separation collection choice infinite core rawWitnesses

theorem choose_groundLayerGraph :
    ∃ W ∈ M.sets, ∃ layers ∈ M.sets, ZFSet.IsFunc (chronologyPairs T) W layers ∧
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
        ZFSet.pair (ZFSet.pair s t) z ∈ layers →
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  have hN := M.omega_mem separation infinite
  have hPairs := M.chronologyPairs_mem pairing unions powers separation fields.time_ground
  have total : ∀ p ∈ chronologyPairs T, ∃ z ∈ M.sets,
      Realize M.sets chronologyLayerRelationFormula
        (extend p (extend z (fields.layerRelationParams ZFSet.omega))) := by
    intro p hp
    obtain ⟨s, hs, t, ht, rfl, earlier⟩ := (mem_chronologyPairs T p).1 hp
    obtain ⟨z, hz, code⟩ := rawWitnesses s hs t ht earlier
    exact ⟨z, hz, (fields.realize_chronologyLayerRelation pairing unions core hN hz hs ht earlier).2 code⟩
  obtain ⟨W, hW, layers, hLayers, function, recognized⟩ :=
    M.choose_definable_relation pairing unions powers separation collection choice
      chronologyLayerRelationFormula (fields.layerRelationParams ZFSet.omega)
      (fields.layerRelationParams_ground hN) hPairs total
  refine ⟨W, hW, layers, hLayers, function, ?_⟩
  intro s hs t ht earlier z entry
  have hz := M.pair_right (M.transitive hLayers entry)
  exact (fields.realize_chronologyLayerRelation pairing unions core hN hz hs ht earlier).1
    (recognized (ZFSet.pair s t) z entry)

theorem exists_serializedChronology (ordinal : ordinalSetProperty T) :
    ∃ serial : GroundSerializedChronology M T C D rD,
      serial.fields = fields ∧ serial.code ∈ M.sets := by
  obtain ⟨W, hW, layers, hLayers, function, codes⟩ :=
    fields.choose_groundLayerGraph pairing unions powers separation collection choice infinite core rawWitnesses
  let serial : GroundSerializedChronology M T C D rD := {
    fields := fields
    ordinal := ordinal
    core := core
    layerBound := W
    layer_bound_ground := hW
    layers := layers
    layers_ground := hLayers
    layer_function := function
    layer_code := codes }
  exact ⟨serial, rfl, serial.code_ground pairing⟩

omit rawWitnesses in
theorem exists_serializedChronology_iff (ordinal : ordinalSetProperty T) :
    (∃ serial : GroundSerializedChronology M T C D rD,
      serial.fields = fields ∧ serial.code ∈ M.sets) ↔
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
        ∃ z ∈ M.sets, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
          (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  constructor
  · rintro ⟨serial, same, _⟩ s hs t ht earlier
    have witness := serial.layer_code s hs t ht earlier _ (serial.layerWitness_entry hs ht earlier)
    rw [same] at witness
    exact ⟨serial.layerWitness s t, serial.layerWitness_ground s t, witness⟩
  · intro witnesses
    exact fields.exists_serializedChronology pairing unions powers separation collection choice infinite core witnesses ordinal

end PartitionPilot.Forcing.GroundChronologyFields

end

end OAI
