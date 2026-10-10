import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixSelectedStepTotality

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def MainPrefixConditionalStepCode (M : TransitiveGround.{u})
    (K Labels C D rD N f old next : ZFSet.{u}) : Prop :=
  MainPrefixSelectedStepCode f old next ∨
    ∃ T S E, old = mainPrefixCode T S E ∧ NonzeroLimitOrdinalCode T ∧
      MainPrefixLimitStepCode M K Labels C D rD N old next

namespace MainPrefixConditionalStepCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N f old next : ZFSet.{u}}
variable (code : MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include code

theorem extension : MainPrefixExtends old next := by
  rcases code with selected | ⟨_, _, _, _, _, limit⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, extension, _⟩ := selected
    exact extension
  · exact limit.extension

theorem next_fields {T S E : ZFSet.{u}} (oldCode : old = mainPrefixCode T S E) :
    ∃ S' E', next = mainPrefixCode (insert T T) S' E' := by
  rcases code with selected | ⟨_, _, _, _, _, limit⟩
  · obtain ⟨b, F, G, F', G', _, _, _, first, second, _⟩ := selected
    have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact ⟨F', G', by simpa only [index] using second⟩
  · obtain ⟨_, _, _, T', S', E', _, nextCode, _⟩ := limit.extension
    exact ⟨S', E', by simpa only [limit.indices_successor oldCode nextCode] using nextCode⟩

theorem selected_of_successor {b S E : ZFSet.{u}}
    (oldCode : old = mainPrefixCode (insert b b) S E) :
    MainPrefixSelectedStepCode f old next := by
  rcases code with selected | ⟨T, F, G, first, limit, _⟩
  · exact selected
  · have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact False.elim (not_nonzeroLimitOrdinalCode_successor b (index.symm ▸ limit))

theorem limit_of_nonzeroLimit {T S E : ZFSet.{u}}
    (oldCode : old = mainPrefixCode T S E) (nonzero : NonzeroLimitOrdinalCode T) :
    MainPrefixLimitStepCode M K Labels C D rD N old next := by
  rcases code with selected | ⟨_, _, _, _, _, limit⟩
  · obtain ⟨b, F, G, _, _, _, _, _, first, _⟩ := selected
    have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact False.elim (not_nonzeroLimitOrdinalCode_successor b (index ▸ nonzero))
  · exact limit

end MainPrefixConditionalStepCode

end PartitionPilot.Forcing

end

end OAI
