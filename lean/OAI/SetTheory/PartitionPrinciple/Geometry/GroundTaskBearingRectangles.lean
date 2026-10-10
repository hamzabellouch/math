import OAI.SetTheory.PartitionPrinciple.Forcing.GroundChronologicalTransitionTransport
import OAI.SetTheory.PartitionPrinciple.Transfinite.LinkedSuccessorOutputFieldEquality

namespace OAI

section

namespace PartitionPilot.Forcing
universe u v

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem rectangles_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    RectangleFulfillmentCode source.main.stage.carrier source.main.stage.actors
      source.main.stage.order source.main.stage.meetGraph source.main.stage.action
      target.main.stage.carrier target.main.stage.actors target.main.stage.order
      target.main.stage.meetGraph target.main.stage.action transition.map.points transition.map.actors := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  exact output.rectangles

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem rectangles_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    RectangleFulfillmentCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      (run.diagram.stage i).stage.action (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.order
      (run.diagram.stage j).stage.meetGraph (run.diagram.stage j).stage.action
      (run.diagram.transition before).map.points (run.diagram.transition before).map.actors := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have strict := actual.rectangles_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    GroundChronologicalMainTransition.retargetEq_actors,
    run.linked_main i, run.linked_main j] using strict

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
