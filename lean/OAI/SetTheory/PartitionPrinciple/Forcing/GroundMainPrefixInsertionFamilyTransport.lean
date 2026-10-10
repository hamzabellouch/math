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

noncomputable def finalInsertionCaps (j : I) (caps : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels (run.diagram.stage j).stage.carrier run.limitPoints caps (run.limitPointMap j)

noncomputable def finalInsertionActors (j : I) (actors : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels (run.diagram.stage j).stage.actors run.limitActors actors (run.limitActorMap j)

theorem finalInsertionCaps_ground (j : I) {caps : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hCaps : caps ∈ M.sets) :
    run.finalInsertionCaps j caps ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels
    (run.diagram.stage j).stage.carrier_ground run.limitPoints_ground hCaps (run.limitPointMap_ground j)

theorem finalInsertionActors_ground (j : I) {actors : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hActors : actors ∈ M.sets) :
    run.finalInsertionActors j actors ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels
    (run.diagram.stage j).stage.actors_ground run.limitActors_ground hActors (run.limitActorMap_ground j)

theorem finalInsertionCaps_injection (j : I) {caps : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps) :
    InjectionCode Labels run.limitPoints (run.finalInsertionCaps j caps) :=
  injection.compose (run.limitPointMap_injection j)

theorem finalInsertionActors_injection (j : I) {actors : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.actors actors) :
    InjectionCode Labels run.limitActors (run.finalInsertionActors j actors) :=
  injection.compose (run.limitActorMap_injection j)

theorem finalInsertionCaps_entry (j : I) {caps label cap' : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps) :
    ZFSet.pair label cap' ∈ run.finalInsertionCaps j caps ↔
      ∃ cap, ZFSet.pair label cap ∈ caps ∧ ZFSet.pair cap cap' ∈ run.limitPointMap j := by
  constructor
  · intro entry
    obtain ⟨_, _, cap, _, old, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact ⟨cap, old, image⟩
  · rintro ⟨cap, old, image⟩
    have oldBounds := ZFSet.pair_mem_prod.1 (injection.function.1 old)
    have imageBounds := ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 image)
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨oldBounds.1, imageBounds.2, cap, oldBounds.2, old, image⟩

theorem finalInsertionActors_entry (j : I) {actors label actor' : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.actors actors) :
    ZFSet.pair label actor' ∈ run.finalInsertionActors j actors ↔
      ∃ actor, ZFSet.pair label actor ∈ actors ∧ ZFSet.pair actor actor' ∈ run.limitActorMap j := by
  constructor
  · intro entry
    obtain ⟨_, _, actor, _, old, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact ⟨actor, old, image⟩
  · rintro ⟨actor, old, image⟩
    have oldBounds := ZFSet.pair_mem_prod.1 (injection.function.1 old)
    have imageBounds := ZFSet.pair_mem_prod.1 ((run.limitActorMap_injection j).function.1 image)
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨oldBounds.1, imageBounds.2, actor, oldBounds.2, old, image⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
