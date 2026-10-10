import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTwoStageMainDiagram

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target first second : GroundChronologicalMainStage M C D rD}

noncomputable def retargetEq
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    GroundChronologicalMainTransition first second := by
  cases sourceEqual
  cases targetEqual
  exact transition

theorem retargetEq_points
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.points = transition.map.points := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_actors
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.actors = transition.map.actors := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_code
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.code = transition.map.code := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_coversOldBirths_iff
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).CoversOldBirths ↔ transition.CoversOldBirths := by
  cases sourceEqual
  cases targetEqual
  rfl

end PartitionPilot.Forcing.GroundChronologicalMainTransition

end

end OAI
