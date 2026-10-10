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

theorem separation_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    SeparationFulfillmentCode source.main.stage.carrier source.main.stage.order
      target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
      target.main.stage.actors target.main.stage.action transition.map.points := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  have separated := output.separation
  simp only [linkedSuccessorOutputFields_0, linkedSuccessorOutputFields_2,
    linkedSuccessorOutputFields_1, linkedSuccessorOutputFields_3,
    linkedSuccessorOutputFields_5, linkedSuccessorOutputFields_7,
    linkedSuccessorOutputFields_13, linkedSuccessorOutputFields_18] at separated
  exact separated

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem separation_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    SeparationFulfillmentCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph
      (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.action
      (run.diagram.transition before).map.points := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have separated := actual.separation_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using separated

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
