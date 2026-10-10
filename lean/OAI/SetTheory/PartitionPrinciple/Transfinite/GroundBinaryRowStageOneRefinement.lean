import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowTermSetNames
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneNameLiftFamilies

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure RefinementStageSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (level T T2 : ZFSet.{u}) : Prop where
  valid1 : ∀ z ∈ T, IsName s z
  valid2 : ∀ z ∈ T2, IsName s z
  terms_hs : ∀ τ : Name s, τ.val ∈ T →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  pairs_hs : ∀ τ : Name s, τ.val ∈ T2 →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  first : NiceNameSystem M a s b d base directed T valid1
  second : NiceNameSystem M a s b d base directed T2 valid2
  indices : NiceRefinementIndexSystem M a s b d level T T2 valid1 valid2
  inputs : StageOneActionParameters M a s t b d T T2 valid1

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem refinementStageSystem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    {level T T2 : ZFSet.{u}} (hLevel : level ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    (closed1 : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (closed2 : ∀ g (τ : Name s), τ.val ∈ T2 → (a.act s g τ).val ∈ T2)
    (children1 : ∀ τ : Name s, τ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ)
    (children2 : ∀ τ : Name s, τ.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ) :
    RefinementStageSystem M a s t b d base directed level T T2 := by
  have first := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT valid1 closed1 b d base directed group nodes supports children1
  have second := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT2 valid2 closed2 b d base directed group nodes supports children2
  have indices := M.niceRefinementIndexSystem a s b d pairing unions powers separation collection
    hLevel hT hT2 carrier order nodes nodeOrder first second
  exact ⟨valid1,valid2,children1,children2,first,second,indices,
    ⟨maps,nodeMaps,closed1,closed2,indices.family_ground⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P Q L : Type u} [Group G]
variable [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q] [PartialOrder L]

structure StageTwoIndexData (M : TransitiveGround.{u})
    (a : PosetAction G P) (s : Presentation P)
    (e : PosetAction G Q) (t : Presentation Q)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Prop where
  next : RefinementStageSystem M e t actors nodes d base directed (natSetCode 1) T T2
  top_code : t.encode ⊤ = s.encode ⊤
  square : T2 = orderedPairNameFamily (t.encode ⊤) T T
  powers : ∀ n : Nat, iteratedPairNameFamily (t.encode ⊤) T n =
    iteratedPairNameFamily (s.encode ⊤) T n
  levels :
    let I0 := M.niceRefinementIndices a s nodes d ∅ T T2 valid
    let I1 := M.niceRefinementIndices e t nodes d (natSetCode 1) T T2 next.valid1
    I0 ∪ I1 ∈ M.sets ∧
      refinementIndexFieldGraph (I0 ∪ I1) {∅, natSetCode 1} 0 ∈ M.sets ∧
      ZFSet.IsFunc (I0 ∪ I1) {∅, natSetCode 1}
        (refinementIndexFieldGraph (I0 ∪ I1) {∅, natSetCode 1} 0) ∧
      refinementIndexFieldGraph (I0 ∪ I1) {∅, natSetCode 1} 0 =
        ZFSet.prod I0 {∅} ∪ ZFSet.prod I1 {natSetCode 1} ∧
      ∀ z, ¬ (z ∈ I0 ∧ z ∈ I1)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (rawRowCarrier I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "levels" => stageTwoAssignmentLevels I0 I1 T

include nodes indices in
theorem stageTwoForcing_entry (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageTwoForcing rawRowCarrier I0 a s b d T T2 valid ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega ∧
      ∃ lower : P, s.encode lower = ZFSet.pair row (assignmentCut levels (natSetCode 1) A) ∧
        M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
          a b d base directed system (natSetCode 1) T2 A lower := by
  rw [M.stageTwoForcing_raw_entry]
  constructor
  · rintro ⟨rowMem, small, lowerMem, raw⟩
    obtain ⟨lower, equal⟩ := (s.mem_carrier _).1 lowerMem
    refine ⟨rowMem, small, lower, equal, ?_⟩
    apply (M.refinementLevelRawTests_iff a s b d (natSetCode 1)
      pairing unions powers separation collection carrier order nodes hT valid indices
      base directed system A lower).1
    exact equal.symm ▸ raw
  · rintro ⟨rowMem, small, lower, equal, tests⟩
    refine ⟨rowMem, small, equal ▸ s.encode_mem lower, ?_⟩
    have raw := (M.refinementLevelRawTests_iff a s b d (natSetCode 1)
      pairing unions powers separation collection carrier order nodes hT valid indices
      base directed system A lower).2 tests
    exact equal ▸ raw

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P Q L : Type u} [Group G]
variable [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q] [PartialOrder L]

structure StageTwoCarrierData (M : TransitiveGround.{u}) (rawRowCarrier rowTop : ZFSet.{u})
    (a : PosetAction G P) (s : Presentation P)
    (e : PosetAction G Q) (t : Presentation Q)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) : Prop where
  index_data : StageTwoIndexData M a s e t actors nodes d base directed T T2 valid
  terms_ground : T ∈ M.sets
  lower_carrier_ground : t.carrier ∈ M.sets
  lower_order_ground : t.conditionOrder ∈ M.sets
  carrier_ground :
    M.stageTwoForcing rawRowCarrier (M.niceRefinementIndices a s nodes d ∅ T T2 valid)
      e t nodes d T T2 index_data.next.valid1 ∈ M.sets
  top_row_mem : rowTop ∈ rawRowCarrier
  empty_top :
    ZFSet.pair rowTop ∅ ∈ M.stageTwoForcing rawRowCarrier
      (M.niceRefinementIndices a s nodes d ∅ T T2 valid) e t nodes d T T2 index_data.next.valid1
  empty_rows : ∀ row ∈ rawRowCarrier, ZFSet.pair row ∅ ∈ t.carrier →
    ZFSet.pair row ∅ ∈ M.stageTwoForcing rawRowCarrier
      (M.niceRefinementIndices a s nodes d ∅ T T2 valid) e t nodes d T T2 index_data.next.valid1
  raw_entries : ∀ row A : ZFSet.{u},
    let I0 := M.niceRefinementIndices a s nodes d ∅ T T2 valid
    let I1 := M.niceRefinementIndices e t nodes d (natSetCode 1) T T2 index_data.next.valid1
    let levels := stageTwoAssignmentLevels I0 I1 T
    ZFSet.pair row A ∈ M.stageTwoForcing rawRowCarrier I0 e t nodes d T T2 index_data.next.valid1 ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega ∧
      ZFSet.pair row (assignmentCut levels (natSetCode 1) A) ∈ t.carrier ∧
      stageOneRawTests M (M.refinementLevelFormulaData e t nodes d (natSetCode 1) T T2 index_data.next.valid1)
        A (ZFSet.pair row (assignmentCut levels (natSetCode 1) A))
  typed_entries : ∀ row A : ZFSet.{u},
    let I0 := M.niceRefinementIndices a s nodes d ∅ T T2 valid
    let I1 := M.niceRefinementIndices e t nodes d (natSetCode 1) T T2 index_data.next.valid1
    let levels := stageTwoAssignmentLevels I0 I1 T
    ZFSet.pair row A ∈ M.stageTwoForcing rawRowCarrier I0 e t nodes d T T2 index_data.next.valid1 ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega ∧
      ∃ lower : Q, t.encode lower = ZFSet.pair row (assignmentCut levels (natSetCode 1) A) ∧
        M.refinementLevelTests t pairing unions powers separation collection
          lower_carrier_ground lower_order_ground terms_ground index_data.next.valid1
          e nodes d base directed index_data.next.first (natSetCode 1) T2 A lower

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (rawRowCarrier rowTop : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (e : PosetAction G Q) (t : Presentation Q)
variable (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

theorem stageTwoCarrierData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (indexData : StageTwoIndexData M a s e t actors nodes d base directed T T2 valid)
    (hRow : rawRowCarrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a s nodes d ∅ T T2 valid ∈ M.sets)
    (hT : T ∈ M.sets) (carrier : t.carrier ∈ M.sets) (order : t.conditionOrder ∈ M.sets)
    (hNodes : nodes.carrier ∈ M.sets) (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (topRow : rowTop ∈ rawRowCarrier) (lowerTop : ZFSet.pair rowTop ∅ ∈ t.carrier) :
    StageTwoCarrierData M rawRowCarrier rowTop a s e t actors nodes d base directed T T2 valid
      pairing unions powers separation collection := by
  let I0 := M.niceRefinementIndices a s nodes d ∅ T T2 valid
  refine ⟨indexData, hT, carrier, order, ?_, topRow, ?_, ?_, ?_, ?_⟩
  · exact M.stageTwoForcing_mem rawRowCarrier I0 e t nodes d T T2 indexData.next.valid1
      pairing unions powers separation hRow hI0 hT carrier order hNodes nodeOrder
      indexData.next.valid2 indexData.next.indices base directed indexData.next.first omega
  · exact M.stageTwoForcing_empty rawRowCarrier I0 e t nodes d T T2 indexData.next.valid1
      hRow topRow lowerTop
  · intro row rowMem lower
    exact M.stageTwoForcing_empty rawRowCarrier I0 e t nodes d T T2 indexData.next.valid1
      hRow rowMem lower
  · exact M.stageTwoForcing_raw_entry rawRowCarrier I0 e t nodes d T T2 indexData.next.valid1
  · exact M.stageTwoForcing_entry rawRowCarrier I0 e t nodes d T T2 indexData.next.valid1
      pairing unions powers separation collection carrier order hNodes hT
      indexData.next.indices base directed indexData.next.first

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets) (t : Presentation G)
variable (inputs : StageOneActionParameters M a c.pairEmpty t b d T T2 valid)
variable (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "smallTop" => M.stageOneConditionSmallTop a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega

theorem stageOneRefinementStageSystem
    (nodeOrder : b.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
    (originalMaps : a.conditionMapFamily c t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    {level : ZFSet.{u}} (hLevel : level ∈ M.sets)
    (children1 : ∀ τ : Name c.pairEmpty, τ.val ∈ T →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) τ)
    (children2 : ∀ τ : Name c.pairEmpty, τ.val ∈ T2 →
      HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) τ) :
    letI := smallOrder
    letI := smallTop
    RefinementStageSystem M (smallAct) (pres) t b d base directed level T T2 := by
  let := smallOrder
  let := smallTop
  obtain ⟨nextValid1,nextClosed1,nextHS1⟩ :=
    M.stageOneNameFamily_transport a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega
      (d.principalSupportFamily base directed) T valid inputs.terms_closed children1
  obtain ⟨nextValid2,nextClosed2,nextHS2⟩ :=
    M.stageOneNameFamily_transport a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega
      (d.principalSupportFamily base directed) T2 valid2 inputs.pairs_closed children2
  have nextCarrier := M.stageOneConditionPresentation_carrier_mem a c b d T T2 valid
    pairing unions powers separation carrier order nodes hT indices base directed system collection nodeOrder omega
  have nextOrder := M.stageOneConditionOrder_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection nodeOrder omega
  have nextMaps := M.stageOneSmallActionMapFamily_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega nodeOrder group originalMaps
  exact M.refinementStageSystem (smallAct) (pres) t b d base directed pairing unions powers separation
    collection nextCarrier nextOrder group nodes nodeOrder nextMaps inputs.node_maps supports
    hLevel hT hT2 nextValid1 nextValid2 nextClosed1 nextClosed2 nextHS1 nextHS2

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order

theorem binaryRowStageOneRefinement {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
      let lifted := Name.renamedFamily c.pairEmpty id T valid
      let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
      ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
        (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
        (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
        (first : NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1)
        (indices : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2)
        (inputs : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid1)
        (_originalMaps : act.conditionMapFamily c b ∈ M.sets),
        let coordinates := M.prod_mem pairing unions powers separation
          (M.nonbottom_carrier_mem s separation hL) hC
        let two := M.natSetCode_mem separation infinite 2
        let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
        let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
        letI := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
          carrier forcingOrder hLifted ⊥ directed first collection
        letI := M.stageOneConditionSmallTop act c s a lifted squared valid1 pairing unions powers separation
          carrier forcingOrder hLifted ⊥ directed first collection
        RefinementStageSystem M
          (M.stageOneSmallAction act c s a lifted squared valid1 pairing unions powers separation
            carrier forcingOrder hLifted indices ⊥ directed first collection b inputs hSquared
            (M.omega_mem separation infinite))
          (M.stageOneConditionPresentation act c s a lifted squared valid1 pairing unions powers separation
            carrier forcingOrder hL hLifted indices ⊥ directed first collection)
          b s a ⊥ directed (natSetCode 1) lifted squared := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2 first indices inputs originalMaps
    coordinates two carrier forcingOrder
  let := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder hLifted ⊥ directed first collection
  let := M.stageOneConditionSmallTop act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder hLifted ⊥ directed first collection
  obtain ⟨children1,children2⟩ := M.binaryRowLiftedTermFamilies_hs a s b C pairing unions powers separation
    infinite hL hC hG graph directed hmu ordinal valid
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation hL hG order graph
  exact M.stageOneRefinementStageSystem act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder hL hLifted indices ⊥ directed first collection b inputs hSquared
    (M.omega_mem separation infinite) order hG originalMaps supports
    (M.natSetCode_mem separation infinite 1) children1 children2

end PartitionPilot.Forcing.TransitiveGround

end OAI
