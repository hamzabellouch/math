import OAI.SetTheory.PartitionPrinciple.Definability.GroundMainFinalSemanticStructuralZF
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecordedPreparationSupportInclusions
import OAI.SetTheory.PartitionPrinciple.Transfinite.StageTwoSupportData

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowDataSelection {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (I anchors : ZFSet.{u}),
      I ∈ M.sets → anchors ∈ M.sets → ZFSet.IsFunc I s.carrier anchors →
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A s.carrier f ∧
      f ⊆ stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
      W = (relationImage A s.carrier f ∪
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
      W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, s.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted I anchors hI hAnchors anchorFunction p A member extra hExtra extraSubset smallExtra
  have nonbottom := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order nonbottom hmu
  have hTuples := M.binaryLiftedRowTupleFamily_mem pairing unions powers separation collection infinite
    hL order nonbottom hC hmu one valid
  obtain ⟨hA,subset,smallA⟩ := (M.mem_groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega A).1 member
  have whole := M.stageOneDataBounds_mem pairing unions powers separation hA hI hLifted hS hL
    hmu nonbottom order hAnchors hTuples
  have total := stageOneDataBounds_total s directed subset anchorFunction
    (liftedRowTupleFamily_surjective c (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
    (fun f hf => by
      obtain ⟨D,hD,bound⟩ := M.rowPositionSequence_bound hf
      obtain ⟨D,rfl⟩ := (s.mem_carrier D).1 hD
      exact ⟨D,bound⟩)
  obtain ⟨hUsed,smallUsed⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite choice nonbottom hC (M.natSetCode_mem separation infinite 2) (SetMembers.raw_mem p)
  have usedSubset : rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) ⊆ s.carrier := by
    intro x hx
    exact ((s.mem_nonbottom_carrier x).1 (rowUsedRows_subset _ _ _ _ hx)).1
  exact M.exists_stageOneDataBound s pairing unions powers separation infinite choice hA hL whole smallA total
    hUsed hExtra usedSubset extraSubset smallUsed smallExtra countable_bound

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 stages history : ZFSet.{u})
local notation "I" => refinementDataHistoryIndices stages
  (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)

theorem structuralIndex_anchor_fields {x : ZFSet.{u}} (member : x ∈ I) :
    ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v 2 ∈ nodes := by
  obtain ⟨level, _hl, data, entry, hx⟩ := (mem_refinementDataHistoryIndices _ _ _).1 member
  obtain ⟨_, P, order, top, action, _stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  obtain ⟨v, equal, bounds⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hx
  exact ⟨v, equal, bounds 2⟩

theorem structuralIndexAnchors_function :
    ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) :=
  refinementIndexFieldGraph_function I nodes 2
    (fun _ member => M.structuralIndex_anchor_fields G nodes nodeOrder basis T T2 stages history member)

include M in
 theorem structuralIndexAnchorData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hs : stages ∈ M.sets) (hh : history ∈ M.sets) :
    I ∈ M.sets ∧ refinementIndexFieldGraph I nodes 2 ∈ M.sets ∧
      ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) := by
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have indices := M.refinementDataHistoryIndices_mem pairing unions powers separation hs packed
  exact ⟨indices, M.refinementIndexFieldGraph_mem pairing unions powers separation indices hn 2,
    M.structuralIndexAnchors_function G nodes nodeOrder basis T T2 stages history⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStructuralDataSelection {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A s.carrier f ∧
      f ⊆ stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
      W = (relationImage A s.carrier f ∪
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
      W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, s.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted G basis T2 stages history hG hb hT2 hs hh I anchors
    p A member extra hExtra extraSubset extraSmall
  obtain ⟨indexGround, anchorGround, anchorFunction⟩ :=
    M.structuralIndexAnchorData G s.carrier s.conditionOrder basis lifted T2 stages history
      pairing unions powers separation collection hG hL order hb hLifted hT2 hs hh
  exact M.binaryRowDataSelection s C pairing unions powers separation collection infinite choice
    hL order hC directed countable_bound hmu one valid hLifted I anchors indexGround anchorGround
    anchorFunction p A member extra hExtra extraSubset extraSmall

theorem binaryRowStructuralConditionDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      ZFSet.pair (c.encode p) A ∈
        M.structuralForcingCarrier c.carrier G s.carrier s.conditionOrder basis lifted T2 stages history →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted G basis T2 stages history hG hb hT2 hs hh I anchors
    p A member extra hExtra extraSubset extraSmall
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages
    (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    (ZFSet.pair (c.encode p) A)).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  obtain ⟨D, _f, _hf, _W, _hW, _function, _selected, _equal, _subset, _small, _bound,
      bounds, usedBound, extraBound⟩ :=
    M.binaryRowStructuralDataSelection s C pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu one valid hLifted G basis T2 stages history
      hG hb hT2 hs hh p A small extra hExtra extraSubset extraSmall
  exact ⟨D, usedBound, bounds, extraBound⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowRecordedPreparationConditionDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      ZFSet.pair (c.encode p) A ∈
        M.structuralForcingCarrier c.carrier G s.carrier s.conditionOrder basis lifted T2 stages history →
    ∀ E events : ZFSet.{u}, E ∈ M.sets → ZFSet.IsFunc ZFSet.omega E events →
    let recorded := M.preparationUsedSupportUnion s.carrier E events
    recorded ∈ M.sets → M.groundEmbeddable recorded ZFSet.omega →
    ∀ extra : ZFSet.{u}, extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    (recorded ∪ extra) ∈ M.sets ∧ (recorded ∪ extra) ⊆ s.carrier ∧
      M.groundEmbeddable (recorded ∪ extra) ZFSet.omega ∧
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ recorded ∪ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted G basis T2 stages history hG hb hT2 hs hh I anchors
    p A member E events hE function recorded hRecorded smallRecorded extra hExtra extraSubset smallExtra
  have recordedSubset : recorded ⊆ s.carrier := by
    intro v hv
    exact ((M.mem_preparationUsedSupportUnion separation hL hE function v).1 hv).1
  have combinedGround := M.binary_union_mem pairing unions hRecorded hExtra
  have combinedSubset : recorded ∪ extra ⊆ s.carrier := by
    intro v hv
    exact (ZFSet.mem_union.1 hv).elim (fun h => recordedSubset h) (fun h => extraSubset h)
  have combinedSmall := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hRecorded hExtra smallRecorded smallExtra
  obtain ⟨D, usedBound, dataBound, combinedBound⟩ :=
    M.binaryRowStructuralConditionDataBound s C pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu one valid hLifted G basis T2 stages history
      hG hb hT2 hs hh p A member (recorded ∪ extra) combinedGround combinedSubset combinedSmall
  exact ⟨combinedGround, combinedSubset, combinedSmall, D, usedBound, dataBound, combinedBound⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowSemanticStructuralBoundHistory
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared stages history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared stages history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared stages history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared stages P order top action ∧
              let J := refinementDataHistoryIndices stages
                (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                  (supportBasisCode s b a.principalFix) lifted squared stages history)
              let anchors := refinementIndexFieldGraph J s.carrier 2
              let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
                (⋃₀ ⋃₀ rows) rows S valid
              ∀ (p : SetMembers (M.smallPartialFunctions
                  (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
                ZFSet.pair (c.encode p) A ∈
                  M.structuralForcingCarrier c.carrier b.carrier s.carrier s.conditionOrder
                    (supportBasisCode s b a.principalFix) lifted squared stages history →
              ∀ extra ∈ M.sets, extra ⊆ s.carrier → M.groundEmbeddable extra ZFSet.omega →
              ∃ E : SetMembers geometry.carrier, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
                ZFSet.IsFunc A s.carrier f ∧
                f ⊆ stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
                W = (relationImage A s.carrier f ∪
                  rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
                W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
                (∀ x : SetMembers geometry.carrier, s.encode x ∈ W → x ≤ E) ∧
                (∀ z ∈ A, ZFSet.pair z (s.encode E) ∈
                  stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
                (∀ x : SetMembers geometry.carrier,
                  s.encode x ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → x ≤ E) ∧
                (∀ x : SetMembers geometry.carrier, s.encode x ∈ extra → x ≤ E) := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  have countableBound := geometry.decoded_countable_bound
    (fun W hW subset small => (fulfilled.countable_localization W hW subset small).2)
  have original := fulfilled.exists_rowSemanticStructuralFinalHistory collection infinite choice hK standard indices
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := original
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, ?_⟩
  intro stages hStages ordinal
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, stageOrder, top, stageAction, code, fields, witness⟩ := histories stages hStages ordinal
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, stageOrder, top, stageAction, code, fields, witness, ?_⟩
  intro p A member extra hExtra extraSubset extraSmall
  have candidate := (M.mem_refinementHistoryForcing c.carrier _ stages _
    (ZFSet.pair (c.encode p) A)).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  exact M.binaryRowStructuralDataSelection s columns pairing unions powers separation collection infinite choice
    geometry.carrier_ground order hColumns directed countableBound hmu ⊤ valid hLifted
    b.carrier (supportBasisCode s b a.principalFix) _ stages history
    geometry.actors_ground supports hSquared hStages hHistory p A small extra hExtra extraSubset extraSmall

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
