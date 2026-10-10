import OAI.SetTheory.PartitionPrinciple.Forcing.GroundChronologicalTransitionTransport
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTaskBearingInsertionFulfillment

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

theorem insertionFamilies_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets)
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (he : e ∈ (run.diagram.stage i).stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ (run.diagram.stage i).stage.order)
    (strict : ZFSet.pair e c ∉ (run.diagram.stage i).stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ (run.diagram.stage i).stage.order) :
    ∃ capFamily ∈ M.sets, ∃ actorFamily ∈ M.sets,
      InjectionCode Labels (run.diagram.stage j).stage.carrier capFamily ∧
      InjectionCode Labels (run.diagram.stage j).stage.actors actorFamily ∧
      (∀ label k top' v, ZFSet.pair label k ∈ actorFamily →
        ZFSet.pair (run.diagram.stage i).stage.top top' ∈ (run.diagram.transition before).map.points →
        (ZFSet.pair (ZFSet.pair k top') v ∈ (run.diagram.stage j).stage.action ↔
          ZFSet.pair label v ∈ capFamily)) ∧
      ∀ c' e', ZFSet.pair c c' ∈ (run.diagram.transition before).map.points →
        ZFSet.pair e e' ∈ (run.diagram.transition before).map.points →
        (∀ label k, ZFSet.pair label k ∈ actorFamily →
          ∀ z ∈ (run.diagram.stage j).stage.carrier,
            ZFSet.pair z c' ∈ (run.diagram.stage j).stage.order →
              ZFSet.pair (ZFSet.pair k z) z ∈ (run.diagram.stage j).stage.action) ∧
        (∀ label k cap, ZFSet.pair label k ∈ actorFamily → ZFSet.pair label cap ∈ capFamily →
          ∀ x x' y, ZFSet.pair x x' ∈ (run.diagram.transition before).map.points →
            ZFSet.pair (ZFSet.pair k x') y ∈ (run.diagram.stage j).stage.action →
              ZFSet.pair y cap ∈ (run.diagram.stage j).stage.order) ∧
        (∀ label cap, ZFSet.pair label cap ∈ capFamily →
          CodedCapProfile (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
            (run.diagram.stage j).stage.meetGraph c' e' cap
            (relationImage F (run.diagram.stage j).stage.carrier
              (run.diagram.transition before).map.points)) ∧
        (∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ capFamily →
          ZFSet.pair second cap₂ ∈ capFamily → first ≠ second →
            ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ (run.diagram.stage j).stage.meetGraph) := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have families := actual.exists_insertionFamilies pairing unions powers separation choice hLabels
    (show c ∈ (run.linked i).main.stage.carrier from by simpa only [run.linked_main i] using hc)
    (show e ∈ (run.linked i).main.stage.carrier from by simpa only [run.linked_main i] using he)
    hF (by simpa only [run.linked_main i] using filter)
    (by simpa only [run.linked_main i] using lower)
    (by simpa only [run.linked_main i] using strict)
    (by simpa only [run.linked_main i] using above)
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using families

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
