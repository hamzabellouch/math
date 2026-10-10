import OAI.SetTheory.PartitionPrinciple.Transfinite.MainPrefixSelectedTraceLaws

namespace OAI

section

namespace PartitionPilot.Forcing.OrdinalRecursionTrace
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD N f B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
variable (chosen : ∀ old next, ZFSet.pair old next ∈ g →
  MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include trace chosen

theorem mainPrefix_selected_successor (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    MainPrefixSelectedStepCode f old next := by
  have entry := trace.mainPrefix_successor_entry ordinal member oldEntry nextEntry
  obtain ⟨S, E, oldCode⟩ := (trace.mainPrefix_values oldEntry).2
  exact (chosen old next entry).selected_of_successor oldCode

theorem mainPrefix_selected_limit (ordinal : ordinalSetProperty A)
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q)
    {α next : ZFSet.{u}} (member : α ∈ A) (limit : NonzeroLimitOrdinalCode α)
    (nextEntry : ZFSet.pair α next ∈ p) :
    ∃ input, MainPrefixHistoryUnionCode (graphRestriction α p) input ∧
      MainPrefixAtIndex α input ∧ ZFSet.pair input next ∈ g ∧
      MainPrefixLimitStepCode M K Labels C D rD N input next := by
  have ordinalIndex := ordinalSetProperty_member ordinal member
  have earlier := trace.restrict ordinalIndex (fun x hx => ordinal.1 α member x hx)
  have history := earlier.preservedMainPrefixHistory candidates
  obtain ⟨input, union, entry⟩ := (trace.2 α member next nextEntry).selected_of_nonzero limit.1
  have equal := union.unique history.union_code
  have atIndex : MainPrefixAtIndex α input := by
    rw [equal]
    refine ⟨history.graphFamily.stageUnion, history.graphFamily.transitionUnion, ?_⟩
    change mainPrefixCode history.graphFamily.indexUnion _ _ = _
    rw [history.graphFamily_indexUnion ordinalIndex]
  obtain ⟨S, E, inputCode⟩ := atIndex
  exact ⟨input, union, ⟨S, E, inputCode⟩, entry,
    (chosen input next entry).limit_of_nonzeroLimit inputCode limit⟩

end PartitionPilot.Forcing.OrdinalRecursionTrace

end

end OAI
