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

theorem strict_top_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    StrictSuccessorTopCode source.main.stage.carrier target.main.stage.carrier
      target.main.stage.order transition.map.points target.main.stage.top := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  have strict := output.strict_top
  rw [linkedSuccessorOutputFields_0, linkedSuccessorOutputFields_1,
    linkedSuccessorOutputFields_3, linkedSuccessorOutputFields_18,
    linkedSuccessorOutputFields_29] at strict
  exact strict

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem strict_top_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
      (run.diagram.transition before).map.points (run.diagram.stage j).stage.top := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have strict := actual.strict_top_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using strict

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
