import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingHistoryConstruction

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)

theorem structuralTrace_finitePowerTerms
    (rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName c.pairEmpty z) (topMem : rowTop ∈ c.carrier)
    {stages history : ZFSet.{u}} (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier rowOrder rowTop rowAction G nodes nodeOrder nodeAction
        basis T T2 level prior) stages history) (n : Nat) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    J ∈ M.sets ∧ ∀ alpha : ZFSet.{u}, ordinalSetProperty alpha → alpha ⊆ stages →
      ∀ z ∈ J, IsName (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed))) z := by
  have oneGround := M.orderedPair_mem pairing (M.transitive carrier topMem)
    (M.empty_mem ⟨c.carrier, carrier⟩)
  have ground := M.iteratedPairNameFamily_mem pairing unions powers separation oneGround hT n
  have original : ∀ z ∈ iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n, IsName c.pairEmpty z := by
    obtain ⟨p, rfl⟩ := (c.mem_carrier rowTop).1 topMem
    exact iteratedPairNameFamily_valid p valid n
  let run := M.structuralForcingTrace_recursiveOrder c.carrier rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 ordinal trace
  refine ⟨ground, ?_⟩
  intro alpha alphaOrdinal subset
  exact M.refinementHistoryRowNameFamily_valid c (run.carriers.restrict alphaOrdinal subset)
    alphaOrdinal carrier (iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n) original

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
