import OAI.SetTheory.PartitionPrinciple.Geometry.InitialCompressionAccounting

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainStage
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD) (Labels : ZFSet.{u})

noncomputable def compressionInitial : RecursiveStateData.{u} :=
  M.initialCompressionData stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

noncomputable def compressionTasks : ZFSet.{u} :=
  M.groundEligibleTasks stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

noncomputable def compressionSources : ZFSet.{u} :=
  literalTaskSourceGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionFilters : ZFSet.{u} :=
  literalTaskFilterGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionTargets : ZFSet.{u} :=
  literalTaskTargetGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionSeparators : ZFSet.{u} :=
  literalTaskSeparatorGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionTaskAction : ZFSet.{u} :=
  M.groundTaskTransport stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

end PartitionPilot.Forcing.GroundMainStage

end

end OAI
