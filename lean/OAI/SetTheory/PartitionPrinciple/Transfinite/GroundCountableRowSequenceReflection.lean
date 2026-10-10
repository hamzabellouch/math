import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralPrefixPreparationInputs

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem countableRow_semanticStructuralTrace_internally_closed
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
      InternallyCountablyClosed M (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T stages packed)) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop action group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows stages history hs hh ordinal trace
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice hX two
  exact M.semanticStructuralTrace_internally_closed c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier order action group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh ordinal trace infinite choice rowClosed






theorem countableRow_semanticStructuralTrace_jointZF_sequenceReflection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) (small : M.sets.Countable) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u})
    (rowAction : a.actionGraph c t ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
    (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (topMem : rowTop ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
    let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
    let omega := M.omega_mem separation infinite
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ stages}
    let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hh hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let act := M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
      M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
    let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
      (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
    let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
      (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
    let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
      M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice
    let s := SetMembers.presentation Q
    let F := d.principalSupportFamily base directed
    ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
      (∀ j : Cuts,
        ((projections j).projectedFilter H).GenericFor
          (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
        ((projections j).projectedFilter H).GenericFor
          (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
      M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) ∧
      (∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M (M.symmetricExtension s (act) F H) U) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice hX two
  exact M.semanticStructuralTrace_jointZF_sequenceReflection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice rowClosed small

end PartitionPilot.Forcing.TransitiveGround

end OAI
