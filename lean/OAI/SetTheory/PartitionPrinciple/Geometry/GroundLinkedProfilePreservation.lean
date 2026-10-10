import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixPreservedSeeds

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target chosenSource chosenTarget : GroundLinkedMainStage M K Labels C D rD}

theorem retargetLinked_preservesOldProfiles_iff
    (transition : GroundChronologicalMainTransition source.main target.main)
    (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code) :
    (transition.retargetLinked sourceCode targetCode).PreservesOldProfiles ↔
      transition.PreservesOldProfiles := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  change OldProfilePreservationCode chosenSource.main.stage.carrier chosenSource.main.stage.order
    chosenSource.main.stage.meetGraph chosenTarget.main.stage.carrier chosenTarget.main.stage.order
    chosenTarget.main.stage.meetGraph transition.map.points (M.groundPower chosenSource.main.stage.carrier) ↔ _
  rw [← first.stage, ← second.stage]
  rfl

theorem preservesOldProfiles_iff_of_map_code
    (first second : GroundChronologicalMainTransition source.main target.main)
    (equal : first.map.code = second.map.code) :
    first.PreservesOldProfiles ↔ second.PreservesOldProfiles := by
  have points : first.map.points = second.map.points := (ZFSet.pair_inj.1 equal).1
  unfold PreservesOldProfiles
  rw [points]

end GroundChronologicalMainTransition

def LinkedProfilePreservingTransitionCode (M : TransitiveGround.{u})
    (K Labels C D rD a b z : ZFSet.{u}) : Prop :=
  ∃ source target : GroundLinkedMainStage M K Labels C D rD,
    source.code = a ∧ target.code = b ∧
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths ∧ transition.PreservesOldProfiles

namespace LinkedProfilePreservingTransitionCode
variable {M : TransitiveGround.{u}} {K Labels C D rD a b z : ZFSet.{u}}

theorem linked_transition (code : LinkedProfilePreservingTransitionCode M K Labels C D rD a b z) :
    LinkedMainTransitionCode M K Labels C D rD a b z := by
  obtain ⟨source, target, first, second, transition, equal, covered, _⟩ := code
  exact ⟨source, target, first, second, transition, equal, covered⟩

theorem exists_at (source target : GroundLinkedMainStage M K Labels C D rD)
    (code : LinkedProfilePreservingTransitionCode M K Labels C D rD source.code target.code z) :
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths ∧ transition.PreservesOldProfiles := by
  obtain ⟨first, second, sourceCode, targetCode, transition, equal, covered, preserved⟩ := code
  exact ⟨transition.retargetLinked sourceCode targetCode,
    (transition.retargetLinked_code sourceCode targetCode).trans equal,
    transition.retargetLinked_coversOldBirths sourceCode targetCode covered,
    (transition.retargetLinked_preservesOldProfiles_iff sourceCode targetCode).2 preserved⟩

theorem preserves_at {source target : GroundLinkedMainStage M K Labels C D rD}
    (transition : GroundChronologicalMainTransition source.main target.main)
    (code : LinkedProfilePreservingTransitionCode M K Labels C D rD
      source.code target.code transition.map.code) : transition.PreservesOldProfiles := by
  obtain ⟨chosen, equal, _, preserved⟩ := code.exists_at source target
  exact (chosen.preservesOldProfiles_iff_of_map_code transition equal).1 preserved

end LinkedProfilePreservingTransitionCode

end PartitionPilot.Forcing

end

end OAI
