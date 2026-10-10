import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAugmentedClassRequests

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_internally_closed
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    InternallyCountablyClosed M (SetMembers.presentation
      (M.refinementHistoryForcing c.carrier T stages packed)) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have unionTests := M.structuralHistory_rawTests_union t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact M.refinementHistory_internally_closed c T stages packed run ordinal unionTests
    pairing unions powers separation infinite choice carrier hT hs hPacked rowClosed

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "Cuts" => {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ≤ stages}
local notation "lower" => (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_jointZF (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
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
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let : Countable M.sets := small
  let intoGround : Cuts → M.sets := fun j => ⟨j.val, j.property.1⟩
  have injective : Function.Injective intoGround := by
    intro j k equal
    apply Subtype.ext
    exact congrArg (fun x : M.sets => x.val) equal
  let : Countable Cuts := injective.countable
  let s := SetMembers.presentation Q
  let F := d.principalSupportFamily base directed
  have hQ : s.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hOrder : s.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have hGraph : (act).actionGraph s t ∈ M.sets := by
    rw [M.semanticStructuralAction_graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
  have maps := M.conditionMapFamily_mem_of_actionGraph (act) s t pairing unions powers separation
    collection hQ group hGraph
  dsimp only
  intro p
  obtain ⟨H, hp, ground, ordinary, symmetric, projected⟩ :=
    M.exists_joint_projection_generic s (act) F small hQ lower
      (fun j => SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))
      (fun j => (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code)
      (fun j => (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code)
      (fun j => M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice) p
  exact ⟨H, hp, ground, ordinary, symmetric, projected,
    M.ground_subset_symmetric_values s (act) F pairing unions powers separation collection hQ H,
    M.symmetric_ZF (act) s t b F d.principalFix (d.principalSupportFamily_basis base directed)
      pairing unions powers separation collection infinite hQ hOrder group nodes supports maps H symmetric⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "Cuts" => {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ≤ stages}
local notation "lower" => (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_sequenceReflection
    (rowClosed : InternallyCountablyClosed M c) (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let s := SetMembers.presentation Q
    ∀ (H : ConditionFilter (SetMembers Q)),
      H.GenericFor (M.codedFamily s) →
      H.GenericFor (formulaFamily (M.nameDomain s)) →
      ∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M
          (M.symmetricExtension s (act) (d.principalSupportFamily base directed) H) U := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let s := SetMembers.presentation Q
  have hQ : s.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hOrder : s.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have closed := M.semanticStructuralTrace_internally_closed c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice rowClosed
  dsimp only
  intro H coded ordinary U hU
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice hQ hOrder small hU closed H coded ordinary
  refine ⟨reflection, ?_⟩
  intro f hf function
  exact reflection f
    (M.symmetricExtension_subset_ordinaryExtension s (act)
      (d.principalSupportFamily base directed) H hf) function

theorem semanticStructuralTrace_jointZF_sequenceReflection
    (rowClosed : InternallyCountablyClosed M c) (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
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
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, projected, contains, zf⟩ :=
    M.semanticStructuralTrace_jointZF c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice small p
  refine ⟨H, hp, coded, ordinary, symmetric, projected, contains, zf, ?_⟩
  exact M.semanticStructuralTrace_sequenceReflection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice rowClosed small H coded ordinary

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 alpha history)
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_preparation_inputs
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    let lower := SetMembers.presentation Q
    lower.carrier ∈ M.sets ∧ lower.conditionOrder ∈ M.sets ∧
    (act).conditionMapFamily lower t ∈ M.sets ∧ InternallyCountablyClosed M lower ∧
    (∀ g (tau : Name lower), tau.val ∈ T → ((act).act lower g tau).val ∈ T) ∧
    (∀ tau : Name lower, tau.val ∈ T →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hT hAlpha hLowerPacked omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, alpha, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hAlpha (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection group hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments rowAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph act lower t pairing unions powers separation
    collection hQ group hGraph
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  have closed := M.semanticStructuralTrace_internally_closed c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
      (trace.restrict cutOrdinal subset) infinite choice rowClosed
  dsimp only at closed
  rw [packedEq] at closed
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, terms, children⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  exact ⟨hQ, hOrder, maps, closed, terms, children⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
