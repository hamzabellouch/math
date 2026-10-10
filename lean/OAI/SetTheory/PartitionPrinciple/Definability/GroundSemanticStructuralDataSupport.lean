import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationLimits
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNamePositionSupports

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

theorem semanticStructuralCurrent_witness
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (P order top action : ZFSet.{u})
    (output : forcingStageCode P order top action =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history) :
    RawRefinementStageWitness M t b d base directed T T2 stages P order top action :=
  structuralForcingStage_witness_step M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    (structuralForcingTrace_witnesses M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace) P order top action output

theorem semanticStructuralCurrent_stage
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history) :
    ∃ P order top action,
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history = forcingStageCode P order top action ∧
      (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
      RawRefinementStageWitness M t b d base directed T T2 stages P order top action := by
  have ground := M.structuralForcingStage_mem pairing unions powers separation collection
    ![c.carrier, c.conditionOrder, rowTop, a.actionGraph c t, t.carrier, b.carrier,
      b.conditionOrder, d.actionGraph b t, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases carrier (Fin.cases rowOrderGround (Fin.cases (M.transitive carrier topMem) (Fin.cases rowAction (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases nodeAction (Fin.cases supports (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))))))) omega
  have equal := M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history
  change M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history ∈ M.sets at ground
  rw [equal] at ground
  exact ⟨_, _, _, _, equal, M.forcingStageCode_fields ground,
    semanticStructuralCurrent_witness M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace _ _ _ _ equal.symm⟩

theorem exists_semanticStructuralFinalHistory
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history ∧
      M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history ∈ M.sets ∧
      RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 stages history) ∧
      (∀ level P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        RawRefinementStageWitness M t b d base directed T T2 level P order top action) ∧
      (∃ P order top action,
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history = forcingStageCode P order top action ∧
      (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
      RawRefinementStageWitness M t b d base directed T T2 stages P order top action) := by
  obtain ⟨history, hh, trace, hPacked, run, witnesses⟩ :=
    exists_semanticStructuralForcingHistory M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs ordinal
  exact ⟨history, hh, trace, hPacked, run, witnesses,
    semanticStructuralCurrent_stage M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace⟩

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
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

theorem semanticStructuralAction_code :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) rawGraph := by
  exact (M.semanticStructuralCurrent_witness c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace _ _ _ _
    (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history).symm).action_code

noncomputable def semanticStructuralAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    PosetAction G (SetMembers Q) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  have code := M.semanticStructuralAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  rw [← M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed] at code
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

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
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_sourceCondition
    {row sourceA : ZFSet.{u}} (source : ZFSet.pair row sourceA ∈ Q) (g : G) :
    let movedA := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA
    sourceA ∈ M.sets ∧ movedA ∈ M.sets ∧
      ∃ movedRow ∈ c.carrier, ZFSet.pair movedRow movedA ∈ Q ∧
        ZFSet.pair (ZFSet.pair (t.encode g) row) movedRow ∈ a.actionGraph c t := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hSource := M.transitive (M.union_mem unions (M.union_mem unions hQ))
    (pair_second_mem_doubleUnion source)
  have imageGround := M.structuralAssignmentImage_mem pairing unions powers separation collection
    group nodes nodeOrder nodeAction supports hT hT2 hs hh (M.transitive group (t.encode_mem g)) hSource
  have rowMember := (ZFSet.pair_mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed source)).1
  obtain ⟨r, rfl⟩ := (c.mem_carrier row).1 rowMember
  let sourceCondition : SetMembers Q := SetMembers.ofMem (ZFSet.pair (c.encode r) sourceA) source
  have coordinates := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace g sourceCondition r sourceA (SetMembers.raw_ofMem _ _)
  have target := SetMembers.raw_mem ((act).iso g sourceCondition)
  rw [coordinates] at target
  exact ⟨hSource, imageGround, c.encode (a.iso g r), c.encode_mem _, target,
    (a.triple_mem_actionGraph c t g r (a.iso g r)).2 rfl⟩

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

theorem semanticStructuralCurrent_assignment_fixed_of_dataBound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (P order top action : ZFSet.{u})
    (output : forcingStageCode P order top action =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history)
    (I S mu X tuples A : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (g : G) (actor : g ∈ d.principalFix D) (z : ZFSet.{u})
    (member : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages 0) T)
    (bound : ZFSet.pair z (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) :
    ZFSet.pair z z ∈ M.rawStageRefinementAssignmentActionGraph (t.encode g)
      P order top action t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages := by
  have equal := output.trans (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have hPacked : packed ∈ M.sets :=
    M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier rowTop topMem topRows
  let s := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
  let e := M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation
    collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
  have coordinates := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem
    topRows hs hh ordinal trace
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g)
  have graph := M.semanticStructuralAction_graph c a t b d base directed T T2 rowTop pairing unions
    powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
    hs hh ordinal trace
  change e.actionGraph s t = _ at graph
  have actionGround : e.actionGraph s t ∈ M.sets := by
    rw [graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection carrier
      rowAction group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
  have system := M.recursiveRefinementStageSystem c a t b d base directed T T2 stages packed run.carriers ordinal
    pairing unions powers separation collection carrier rowOrderGround group nodes nodeOrder nodeMaps supports
    hT hT2 hs hPacked omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows
    e image coordinates emptyImage actionGround
  have liftedSupport := a.positionSupport_of_codeLift c.pairEmpty e s
    (M.refinementHistoryRowNameLift c run.carriers ordinal carrier)
    (M.refinementHistoryRowNameLift_val c run.carriers ordinal carrier)
    (M.refinementHistoryRowNameLift_stabilizer c run.carriers ordinal carrier a e image coordinates emptyImage)
    T valid1 b d S mu X tuples D range support
  have hQ : s.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have orderEq : s.conditionOrder = M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have nextOrder : s.conditionOrder ∈ M.sets := by
    rw [orderEq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have topEq : s.encode ⊤ = ZFSet.pair rowTop ∅ :=
    M.refinementHistoryDecodedTop_eq c.conditionOrder_code T stages packed
      run.carriers ordinal carrier rowTop topMem topRows
  have typedMember : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (e.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 stages 0) T := by
    rw [orderEq, topEq, graph]
    exact member
  have fixed := M.rawStageRefinementAssignment_fixed_of_dataBound e s t b d base directed stages T T2
    system pairing unions powers separation collection hQ nextOrder group nodes supports hs hT
    I S mu X tuples A D liftedSupport g actor z typedMember bound
  rw [orderEq, topEq, graph] at fixed
  exact fixed

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
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "J" => M.structuralAssignments t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "assignmentGraph" => M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAssignment_relationLaws :
    RelationActionLaws G J (fun g => rawActionSection (t.encode g) assignmentGraph J) := by
  apply M.structuralAssignment_relationLaws t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history trace.1
  intro level _hl P order top action stored
  have fields := M.nonemptyTupleCode_field_mem 4 ![level, P, order, top, action] (M.transitive hh stored)
  exact (M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace level P order top action stored).relationLaws
    pairing unions powers separation collection (fields 1) group nodes (fields 2) supports (fields 0) hT

theorem semanticStructuralAssignmentImage_eq_of_fixed (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ J)
    (fixed : ∀ z ∈ A, ZFSet.pair (ZFSet.pair (t.encode g) z) z ∈ assignmentGraph) :
    M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A = A := by
  have function : FunctionGraphOn J (rawActionSection (t.encode g) assignmentGraph J) :=
    ⟨J, (M.semanticStructuralAssignment_relationLaws c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace).function g⟩
  have self (z : ZFSet.{u}) (hz : z ∈ A) :
      ZFSet.pair z z ∈ rawActionSection (t.encode g) assignmentGraph J :=
    (pair_mem_rawActionSection _ _ _ _ _).2 ⟨subset hz, subset hz, fixed z hz⟩
  change relationImage A J (rawActionSection (t.encode g) assignmentGraph J) = A
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, z, hz, edge⟩ := (mem_relationImage A J _ y).1 member
    exact (function.unique edge (self z hz)).symm ▸ hz
  · intro hy
    exact (mem_relationImage A J _ y).2 ⟨subset hy, y, hy, self y hy⟩

theorem semanticStructuralAction_fixed_iff :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      ((act).iso g p = p ↔ a.iso g r = r ∧
        M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A = A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have moved := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g p r A code
  constructor
  · intro fixed
    have same := moved.symm.trans ((congrArg SetMembers.raw fixed).trans code)
    have parts := ZFSet.pair_inj.1 same
    exact ⟨c.injective parts.1, parts.2⟩
  · rintro ⟨row, data⟩
    apply SetMembers.raw_injective Q
    rw [moved, row, data, ← code]

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

theorem semanticStructuralAssignment_fixed_of_dataBound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (I S mu X tuples A : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (g : G) (actor : g ∈ d.principalFix D) (z : ZFSet.{u})
    (member : z ∈ M.structuralAssignments t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (bound : ZFSet.pair z (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) :
    ZFSet.pair (ZFSet.pair (t.encode g) z) z ∈ M.structuralAssignmentActionGraph
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history := by
  obtain ⟨level, hLevel, P, order, top, action, stored, branchMember⟩ :=
    (M.mem_structuralAssignments t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history z).1 member
  obtain ⟨groundLevel, levelOrdinal, prefixGround, prefixTrace, _fields⟩ :=
    M.structuralTrace_prefix_ground t b d c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      T T2 unions separation hs hh ordinal trace stored
  have fixed := M.semanticStructuralCurrent_assignment_fixed_of_dataBound c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
    nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows groundLevel prefixGround levelOrdinal prefixTrace
    P order top action (trace.2 level hLevel _ stored)
    I S mu X tuples A D range support g actor z branchMember bound
  exact (M.pair_mem_structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) z z).2
    ⟨t.encode_mem g, level, hLevel, P, order, top, action, stored, fixed⟩

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
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "J" => M.structuralAssignments t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "assignmentGraph" => M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

local notation "I" => refinementDataHistoryIndices stages packed
variable (S mu X tuples : ZFSet.{u}) (D : L)
variable (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
variable (support : ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
  RowPositionBound mu X b.conditionOrder f (b.encode D) →
  d.principalFix D ≤ a.stabilizer c.pairEmpty u)
include range support

theorem semanticStructuralAssignmentImage_eq_of_dataBound (g : G) (actor : g ∈ d.principalFix D)
    {A : ZFSet.{u}} (subset : A ⊆ J)
    (bound : ∀ z ∈ A, ZFSet.pair z (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) :
    M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A = A := by
  apply M.semanticStructuralAssignmentImage_eq_of_fixed c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g subset
  intro z hz
  exact M.semanticStructuralAssignment_fixed_of_dataBound c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace I S mu X tuples A D
    range support g actor z (subset hz) (bound z hz)

theorem semanticStructuralCondition_fixed_of_dataBound :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G), g ∈ d.principalFix D →
    ∀ (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A → a.iso g r = r →
      (∀ z ∈ A, ZFSet.pair z (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X
        b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) →
      (act).iso g p = p := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g actor p r A code row bound
  have member := code ▸ SetMembers.raw_mem p
  have candidate := (M.mem_refinementHistoryForcing c.carrier T stages packed _).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  have subset : A ⊆ J := ((M.mem_groundSmallSubsets (stageOneAssignments I T) ZFSet.omega A).1 small).2.1
  exact (M.semanticStructuralAction_fixed_iff c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g p r A code).2
    ⟨row, M.semanticStructuralAssignmentImage_eq_of_dataBound c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace S mu X tuples D range support g actor subset bound⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
