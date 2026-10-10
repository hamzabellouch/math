import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyLayerRelation
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyPairRanks

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
include pairing unions powers separation

theorem choose_layerGraph_in
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {V : ZFSet.{u}} (hV : V ∈ M.sets)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ V, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ layers ∈ M.sets, ZFSet.IsFunc (chronologyPairs T) V layers ∧
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
        ZFSet.pair (ZFSet.pair s t) z ∈ layers →
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  have hN := M.omega_mem separation infinite
  have hPairs := M.chronologyPairs_mem pairing unions powers separation fields.time_ground
  let relation := M.definableRelation chronologyLayerRelationFormula
    (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V
  have hRelation : relation ∈ M.sets := M.definableRelation_mem pairing unions powers separation
    chronologyLayerRelationFormula (fields.layerRelationParams ZFSet.omega)
    (fields.layerRelationParams_ground hN) hPairs hV
  have total : ∀ p ∈ chronologyPairs T, ∃ z ∈ V, ZFSet.pair p z ∈ relation := by
    intro p hp
    obtain ⟨s, hs, t, ht, rfl, earlier⟩ := (mem_chronologyPairs T p).1 hp
    obtain ⟨z, hz, code⟩ := rawWitnesses s hs t ht earlier
    exact ⟨z, hz, (M.pair_mem_definableRelation chronologyLayerRelationFormula
      (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V _ z).2
        ⟨hp, hz, (fields.realize_chronologyLayerRelation pairing unions core hN
          (M.transitive hV hz) hs ht earlier).2 code⟩⟩
  obtain ⟨layers, hLayers, function, subset⟩ :=
    M.uniformize_relation pairing unions powers separation choice hPairs hV hRelation total
  refine ⟨layers, hLayers, function, ?_⟩
  intro s hs t ht earlier z entry
  have recognized := (M.pair_mem_definableRelation chronologyLayerRelationFormula
    (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V _ z).1 (subset entry)
  exact (fields.realize_chronologyLayerRelation pairing unions core hN
    (M.transitive hV recognized.2.1) hs ht earlier).1 recognized.2.2

theorem choose_rankedLayerGraph
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K V : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (hV : V ∈ M.sets)
    (level : ∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < ZFSet.rank K ∧
        GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
          (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ layers ∈ M.sets, ZFSet.IsFunc (chronologyPairs T) V layers ∧
      ZFSet.rank layers < ZFSet.rank K ∧
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
        ZFSet.pair (ZFSet.pair s t) z ∈ layers →
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  have witnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ V, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
    intro s hs t ht earlier
    obtain ⟨z, hz, rank, code⟩ := rawWitnesses s hs t ht earlier
    exact ⟨z, (level z).2 ⟨hz, rank⟩, code⟩
  obtain ⟨layers, hLayers, function, codes⟩ :=
    fields.choose_layerGraph_in pairing unions powers separation infinite choice hV core witnesses
  have rank := conditions.functionGraph_rank_lt_small_cumulative pairing unions powers separation
    collection infinite hK (M.chronologyPairs_mem pairing unions powers separation fields.time_ground)
    (conditions.chronologyPairs_below pairing unions powers separation hK hT)
    (fun _ hp => conditions.chronologyPairs_member_rank_lt pairing unions powers separation hK hT infinite hp)
    hLayers function level
  exact ⟨layers, hLayers, function, rank, codes⟩

end PartitionPilot.Forcing.GroundChronologyFields

end

end OAI
