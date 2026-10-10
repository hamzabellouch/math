import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowIndexedCarriers
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitGroupLaws

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
variable (indices : GroundBelow M run.indices K)
include choice hK standard indices

theorem carrierUnion_below : GroundBelow M run.carrierUnion K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  change GroundBelow M (ZFSet.sUnion (ZFSet.range (fun i => (run.diagram.stage i).stage.carrier))) K
  rw [familyCodeGraph_valueRange_eq run.key _]
  apply GroundBelow.indexed_sUnion pairing unions powers separation choice run.indices_ground
    (M.union_mem unions (M.union_mem unions run.carrierFamily_ground)) run.carrierFamily_ground hK
    conditions.1 conditions.2.2.1 conditions.2.2.2 indices run.carrierFamily_function.to_isFunc
  intro i A entry
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph run.key
    (fun j => (run.diagram.stage j).stage.carrier) _).1 entry
  have value : A = (run.diagram.stage j).stage.carrier := (ZFSet.pair_inj.1 equal).2.symm
  rw [value]
  simpa only [run.linked_main] using (run.linked j).invariant.points_small

theorem actorUnion_below : GroundBelow M run.actorUnion K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  change GroundBelow M (ZFSet.sUnion (ZFSet.range (fun i => (run.diagram.stage i).stage.actors))) K
  rw [familyCodeGraph_valueRange_eq run.key _]
  apply GroundBelow.indexed_sUnion pairing unions powers separation choice run.indices_ground
    (M.union_mem unions (M.union_mem unions run.actorFamily_ground)) run.actorFamily_ground hK
    conditions.1 conditions.2.2.1 conditions.2.2.2 indices run.actorFamily_function.to_isFunc
  intro i A entry
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph run.key
    (fun j => (run.diagram.stage j).stage.actors) _).1 entry
  have value : A = (run.diagram.stage j).stage.actors := (ZFSet.pair_inj.1 equal).2.symm
  rw [value]
  simpa only [run.linked_main] using (run.linked j).invariant.actors_small

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
variable (indices : GroundBelow M run.indices K)
include choice hK standard indices

theorem limitPointLabels_below : GroundBelow M run.limitPointLabels K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierLabels pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.carrierFamily_ground hK conditions.1 conditions.2.2.2 indices
    (run.carrierUnion_below choice hK standard indices)

theorem limitActorLabels_below : GroundBelow M run.limitActorLabels K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierLabels pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorFamily_ground hK conditions.1 conditions.2.2.2 indices
    (run.actorUnion_below choice hK standard indices)

theorem limitPoints_below : GroundBelow M run.limitPoints K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierClasses pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.carrierFamily_ground run.limitPointRelation_ground hK
    conditions.1 conditions.2.2.2 indices (run.carrierUnion_below choice hK standard indices)

theorem limitActors_below : GroundBelow M run.limitActors K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact GroundBelow.indexedCarrierClasses pairing unions powers separation run.indices_ground
    run.actorUnion_ground run.actorFamily_ground run.limitActorRelation_ground hK
    conditions.1 conditions.2.2.2 indices (run.actorUnion_below choice hK standard indices)

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
