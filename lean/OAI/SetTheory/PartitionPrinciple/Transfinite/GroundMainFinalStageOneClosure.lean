import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStageOneForcing
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneFlatConditions

namespace OAI

open scoped ZFSet

section

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
variable (collection : CollectionSchema M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "Q" => M.stageOneForcing a c b d T T2 valid
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) ZFSet.omega
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

local notation "row" => M.stageOneConditionRow a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "data" => M.stageOneConditionData a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (nodeOrder : b.conditionOrder ∈ M.sets)
variable (closed : InternallyCountablyClosed M c)

include infinite choice nodeOrder closed in
theorem stageOneCondition_lower_bound :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection
    ∀ seq : Nat → Shrink Condition,
      natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets → Antitone seq →
      ∃ q : Shrink Condition,
        ((equivShrink Condition).symm q).assignments =
          stageOneAssignmentUnion (fun n => ((equivShrink Condition).symm (seq n)).assignments) ∧
        ∀ n, q ≤ seq n := by
  let := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection
  intro seq whole decreasing
  let typed : Nat → Condition := fun n => (equivShrink Condition).symm (seq n)
  have typedDecreasing : Antitone typed := fun _ _ less => decreasing less
  have rowDecreasing : Antitone (fun n => row (seq n)) :=
    fun _ _ less => (typedDecreasing less).1
  obtain ⟨rowGround, dataGround⟩ := M.stageOneSequence_projections_ground a c b d T T2 valid
    pairing unions powers separation carrier order nodes hT indices base directed system collection
    nodeOrder (M.omega_mem separation infinite) seq whole
  obtain ⟨p, below⟩ := closed (fun n => row (seq n)) rowGround rowDecreasing
  have hJ := M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT
  have smallRaw := M.groundSmallSubset_union_mem pairing unions powers separation infinite choice
    hJ (fun n => data (seq n)) dataGround
  have small : stageOneAssignmentUnion (fun n => (typed n).assignments) ∈ B := by
    simpa only [M.stageOneConditionData_raw] using smallRaw
  let lower : Condition := StageOneCondition.chainUnion M c.pairEmpty pairing unions powers separation
    collection pairedCarrier pairedOrder hT valid a b d base directed system T2
    typed typedDecreasing p below small
  refine ⟨equivShrink Condition lower, ?_, ?_⟩
  · rw [Equiv.symm_apply_apply]
    rfl
  · intro n
    change (equivShrink Condition).symm (equivShrink Condition lower) ≤ typed n
    rw [Equiv.symm_apply_apply]
    exact StageOneCondition.chainUnion_le M c.pairEmpty pairing unions powers separation collection
      pairedCarrier pairedOrder hT valid a b d base directed system T2
      typed typedDecreasing p below small n

include infinite choice nodeOrder closed in
theorem stageOneCondition_internally_closed :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection
    InternallyCountablyClosed M (pres) := by
  let := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection
  intro seq whole decreasing
  obtain ⟨q, _, below⟩ := M.stageOneCondition_lower_bound a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection infinite choice nodeOrder closed seq whole decreasing
  exact ⟨q, below⟩

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

theorem exists_rowStageOneOrder
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
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1 ∧
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2 ∧
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            M.stageOneForcingOrder act c s a lifted squared valid1 ∈ M.sets ∧
            (∀ C E (U Rf Rc : (M.nameDomain c.pairEmpty).names),
              refinementIndexCode ∅ (s.encode C) (s.encode E) U.val.val Rf.val.val Rc.val.val ∈
                M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid1 →
              RefinementObjectSystem M act c.pairEmpty (a.principalSupportFamily ⊥ directed)
                (a.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
            ∀ n : Nat, Name.renamedFamily c.pairEmpty id (iteratedPairNameFamily (c.encode ⊤) T n)
                (iteratedPairNameFamily_valid ⊤ valid n) =
              iteratedPairNameFamily (c.pairEmpty.encode ⊤) lifted n := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
      liftedGround, squaredGround, graphGround, injection, valid1, valid2,
      first, second, indexSystem, forcingGround, objects, finitePowers⟩ :=
    fulfilled.exists_rowStageOneForcing collection infinite choice hK standard indices
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, forcingGround, ?_, objects, finitePowers⟩
  exact M.stageOneForcingOrder_mem act c s a _ _ valid1 pairing unions powers separation
    carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first
    order (M.omega_mem separation infinite)

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment



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

theorem exists_rowStageOneClosure
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
    let hCoordinates := M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
    let hTwo := M.natSetCode_mem separation infinite 2
    let hRow := M.countablePartialFunctions_mem pairing unions powers separation infinite hCoordinates hTwo
    let hOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite hCoordinates hTwo
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
        (∃ hLifted : lifted ∈ M.sets, squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            ∃ first : NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            ∃ indexSystem : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2,
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            M.stageOneForcingOrder act c s a lifted squared valid1 ∈ M.sets ∧
            (letI := M.stageOneConditionSmallOrder act c s a lifted squared valid1
              pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
             InternallyCountablyClosed M
              (M.stageOneConditionPresentation act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection)) ∧
            (∀ C E (U Rf Rc : (M.nameDomain c.pairEmpty).names),
              refinementIndexCode ∅ (s.encode C) (s.encode E) U.val.val Rf.val.val Rc.val.val ∈
                M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid1 →
              RefinementObjectSystem M act c.pairEmpty (a.principalSupportFamily ⊥ directed)
                (a.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
            ∀ n : Nat, Name.renamedFamily c.pairEmpty id (iteratedPairNameFamily (c.encode ⊤) T n)
                (iteratedPairNameFamily_valid ⊤ valid n) =
              iteratedPairNameFamily (c.pairEmpty.encode ⊤) lifted n) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
      liftedGround, squaredGround, graphGround, injection, valid1, valid2,
      first, second, indexSystem, forcingGround, orderGround, objects, finitePowers⟩ :=
    fulfilled.exists_rowStageOneOrder collection infinite choice hK standard indices
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, forcingGround, orderGround, ?_, objects, finitePowers⟩
  exact M.stageOneCondition_internally_closed act c s a _ _ valid1 pairing unions powers separation
    carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first collection
    infinite choice order
    (M.countable_function_internally_closed pairing unions powers separation infinite choice coordinates two)

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
