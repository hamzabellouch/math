import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationLimits

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem countableRow_semanticStructuralTrace_exact_assignment_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      a.actionGraph c t ∈ M.sets →
      t.carrier ∈ M.sets → b.carrier ∈ M.sets → b.conditionOrder ∈ M.sets →
      d.actionGraph b t ∈ M.sets → d.conditionMapFamily b t ∈ M.sets →
      supportBasisCode b t d.principalFix ∈ M.sets → T ∈ M.sets → T2 ∈ M.sets →
      (∀ z ∈ T, IsName c.pairEmpty z) → (∀ z ∈ T2, IsName c.pairEmpty z) →
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T) →
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2) →
      (∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) →
      (∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) →
      rowTop ∈ c.carrier → (∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder) →
      ∀ stages history : ZFSet.{u}, stages ∈ M.sets → history ∈ M.sets →
      ordinalSetProperty stages →
      OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history →
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
      let Q := M.refinementHistoryForcing c.carrier T stages packed
      let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
      let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
      let row := flatCarrierRow c Q B shape
      let data := flatCarrierData c Q B shape
      ∀ seq : Nat → SetMembers Q, groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ q : SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega),
          (∀ n, q ≤ row (seq n)) ∧ ∃ p : SetMembers Q,
          SetMembers.raw p = ZFSet.pair (c.encode q)
            (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∧
          (∀ n, p ≤ seq n) ∧
          SetMembers.raw (data p) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
          stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
          ∀ z, z ∈ SetMembers.raw (data p) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n)) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop action group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows stages history hs hh ordinal trace
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice hX two
  exact M.semanticStructuralTrace_exact_assignment_union c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier order action group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh ordinal trace infinite choice rowClosed

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
