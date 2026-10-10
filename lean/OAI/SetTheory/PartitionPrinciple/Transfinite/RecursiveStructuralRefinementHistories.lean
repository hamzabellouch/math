import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementBinaryUnions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 rows rowOrder stages history : ZFSet.{u})

 theorem structuralRefinementHistory_recursiveOrder
    (ordinal : ordinalSetProperty stages) (function : FunctionGraphOn stages history)
    (shape : ∀ level ∈ stages, ∃ P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (equations : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      P = M.refinementHistoryForcing rows T level
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history)) ∧
      order = M.refinementHistoryOrder rows rowOrder T level
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history))) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  have prefixes {level : ZFSet.{u}} (hl : level ∈ stages) :
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 level (graphRestriction level history) =
      graphRestriction level (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
    rw [M.structuralRefinementHistory_history_restrict,
      M.structuralRefinementHistory_domain_restrict G nodes nodeOrder basis T T2 (ordinal.1 level hl)]
  refine ⟨⟨M.structuralRefinementHistory_dataHistory G nodes nodeOrder basis T T2 stages history function shape, ?_⟩, ?_⟩
  · intro level data entry
    obtain ⟨hl, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact (equations level P order top action stored).1.trans
      (congrArg (M.refinementHistoryForcing rows T level) (prefixes hl))
  · intro level data entry
    obtain ⟨hl, P, order, top, action, stored, rfl⟩ :=
      M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
    exact (equations level P order top action stored).2.trans
      (congrArg (M.refinementHistoryOrder rows rowOrder T level) (prefixes hl))

theorem structuralRefinementHistory_recursiveOrder_of_trace
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history)
    (correct : ∀ level prior stage, step level prior stage → ∃ top action,
      stage = forcingStageCode
        (M.refinementHistoryForcing rows T level
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level prior))
        (M.refinementHistoryOrder rows rowOrder T level
          (M.structuralRefinementHistory G nodes nodeOrder basis T T2 level prior)) top action) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply M.structuralRefinementHistory_recursiveOrder G nodes nodeOrder basis T T2 rows rowOrder stages history ordinal trace.1
  · intro level hl
    obtain ⟨stage, stored⟩ := trace.1.total hl
    obtain ⟨top, action, equal⟩ := correct level _ stage (trace.2 level hl stage stored)
    exact ⟨_, _, top, action, equal ▸ stored⟩
  · intro level P order top action stored
    obtain ⟨top', action', equal⟩ := correct level _ _
      (trace.2 level (trace.1.pair_source stored) _ stored)
    have fields := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
    exact ⟨fields.1, fields.2.1⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
