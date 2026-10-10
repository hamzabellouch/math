import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStageTwoNameLifting

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeCarrierData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  name_lifting : StageTwoNameLiftingData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  construction :
    let actionData := name_lifting.support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
        next.indices.levelCode
      ∃ hNodes : nodes.carrier ∈ M.sets,
      ∃ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first
        let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first a image inputs
        ∃ next2 : RefinementStageSystem M action pres actors nodes d base directed (natSetCode 2) T T2,
          let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
          let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
          let levels := stageThreeAssignmentLevels I0 I1 I2 T
          let Q3 := M.stageThreeForcing c.carrier I0 I1 action pres nodes d T T2 next2.valid1
          ∃ hCarrier : pres.carrier ∈ M.sets, ∃ hOrder : pres.conditionOrder ∈ M.sets,
          T2 = orderedPairNameFamily (pres.encode ⊤) T T ∧
          (∀ n : Nat, iteratedPairNameFamily (pres.encode ⊤) T n =
            iteratedPairNameFamily (s.encode ⊤) T n) ∧
          (∀ C E (U Rf Rc : (M.nameDomain pres).names),
            refinementIndexCode (natSetCode 2) (nodes.encode C) (nodes.encode E)
              U.val.val Rf.val.val Rc.val.val ∈ I2 →
            RefinementObjectSystem M action pres (d.principalSupportFamily base directed)
              (d.principalFix C) T next2.valid1 U.val Rf.val Rc.val) ∧
          (((I0 ∪ I1) ∪ I2) ∈ M.sets ∧
            refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 ∈ M.sets ∧
            levels ∈ M.sets ∧
            ZFSet.IsFunc ((I0 ∪ I1) ∪ I2) (natSetCode 3)
              (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0) ∧
            ZFSet.IsFunc (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) (natSetCode 3) levels ∧
            refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 =
              (ZFSet.prod I0 {∅} ∪ ZFSet.prod I1 {natSetCode 1}) ∪ ZFSet.prod I2 {natSetCode 2} ∧
            levels = (ZFSet.prod (stageOneAssignments I0 T) {∅} ∪
              ZFSet.prod (stageOneAssignments I1 T) {natSetCode 1}) ∪
              ZFSet.prod (stageOneAssignments I2 T) {natSetCode 2} ∧
            (∀ x, ¬ (x ∈ I0 ∧ x ∈ I1)) ∧ (∀ x, ¬ (x ∈ I0 ∧ x ∈ I2)) ∧
              (∀ x, ¬ (x ∈ I1 ∧ x ∈ I2))) ∧
          (∀ A, assignmentCut levels (natSetCode 1) A =
            ZFSet.sep (fun z => z ∈ stageOneAssignments I0 T) A) ∧
          (∀ A, assignmentCut levels (natSetCode 2) A =
            ZFSet.sep (fun z => z ∈ stageOneAssignments (I0 ∪ I1) T) A) ∧
          (∀ A, assignmentCut levels (natSetCode 1) (assignmentCut levels (natSetCode 2) A) =
            assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A) ∧
          (∀ Aq Ap, Aq ⊆ stageOneAssignments (I0 ∪ I1) T →
            assignmentCut levels (natSetCode 2) (assignmentSplice levels (natSetCode 2) Aq Ap) = Aq) ∧
          Q3 ∈ M.sets ∧
          ZFSet.pair (c.encode ⊤) ∅ ∈ Q3 ∧
          (∀ row ∈ c.carrier, ZFSet.pair row ∅ ∈ pres.carrier → ZFSet.pair row ∅ ∈ Q3) ∧
          (∀ row A, ZFSet.pair row A ∈ Q3 ↔
            row ∈ c.carrier ∧ A ∈ M.groundSmallSubsets
              (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega ∧
            ZFSet.pair row (assignmentCut levels (natSetCode 2) A) ∈ pres.carrier ∧
            stageOneRawTests M (M.refinementLevelFormulaData action pres nodes d
              (natSetCode 2) T T2 next2.valid1) A (ZFSet.pair row (assignmentCut levels (natSetCode 2) A))) ∧
          (∀ row A, ZFSet.pair row A ∈ Q3 ↔
            row ∈ c.carrier ∧ A ∈ M.groundSmallSubsets
              (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega ∧
            ∃ lower : Shrink Condition, pres.encode lower = ZFSet.pair row (assignmentCut levels (natSetCode 2) A) ∧
              M.refinementLevelTests pres pairing unions powers separation collection
                hCarrier hOrder prior.terms_ground next2.valid1
                action nodes d base directed next2.first (natSetCode 2) T2 A lower)

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageThreeCarrierData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageTwoNameLiftingData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (hT2 : T2 ∈ M.sets)
    (rows : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (group : actors.carrier ∈ M.sets) (nodeAction : d.actionGraph nodes actors ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageThreeCarrierData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.support_data.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, _, _, _, maps, _⟩ := actionData.actions
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first F first second
  let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
  let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first a image inputs
  have hCarrier : pres.carrier ∈ M.sets := data.carrier_ground
  have hOrder : pres.conditionOrder ∈ M.sets :=
    M.stageTwoConditionOrder_mem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
      rows hI0 rowOrder nodeOrder (M.omega_mem separation infinite)
  have supports := M.principalSupportBasis_mem d nodes actors pairing unions powers separation
    hNodes group nodeOrder nodeAction
  have next2 := M.stageTwoRefinementStageSystem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs
    infinite choice hI0 next.indices.index_ground actors next.inputs hT2 rows rowOrder nodeOrder
    group maps supports next.terms_hs next.pairs_hs
  refine ⟨prior, F, hNodes, inputs, next2, hCarrier, hOrder, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [M.stageTwo_orderedPairNameFamily c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second]
    exact data.index_data.square
  · exact M.stageTwo_iteratedPairNameFamily c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second T
  · exact M.stageTwoRefinementObjects c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs
      infinite hI0 actors next2 hT2 rows rowOrder nodeOrder
  · exact M.stageThreeLevelData pairing unions powers separation hI0 next.indices.index_ground
      next2.indices.index_ground data.terms_ground first second next2.indices.levelCode
  · exact stageThreeAssignmentCut_one first second next2.indices.levelCode
  · exact stageThreeAssignmentCut_two first second next2.indices.levelCode
  · intro A
    rw [stageThreeAssignmentCut_one_old first second next2.indices.levelCode,
      stageThreeAssignmentCut_nested first second next2.indices.levelCode,
      stageThreeAssignmentCut_one_old first second next2.indices.levelCode]
  · intro Aq Ap old
    exact stageThreeAssignmentSplice_lower_eq first second next2.indices.levelCode Ap old
  · exact M.stageThreeForcing_mem c.carrier I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation rows hI0 next.indices.index_ground data.terms_ground
      hCarrier hOrder hNodes nodeOrder next2.valid2 next2.indices base directed next2.first
      (M.omega_mem separation infinite)
  · exact M.stageThreeForcing_empty c.carrier I0 I1 action pres nodes d T T2 next2.valid1
      rows (c.encode_mem ⊤) data.empty_top
  · intro row member lower
    exact M.stageThreeForcing_empty c.carrier I0 I1 action pres nodes d T T2 next2.valid1
      rows member lower
  · exact M.stageThreeForcing_raw_entry c.carrier I0 I1 action pres nodes d T T2 next2.valid1
  · exact M.stageThreeForcing_entry c.carrier I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeProjectionData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  carrier_data : StageThreeCarrierData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  projections :
    let actionData := carrier_data.name_lifting.support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
        next.indices.levelCode
      ∃ hNodes : nodes.carrier ∈ M.sets,
      ∃ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first
        let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first a image inputs
        ∃ next2 : RefinementStageSystem M action pres actors nodes d base directed (natSetCode 2) T T2,
          let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
          let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
          let levels := stageThreeAssignmentLevels I0 I1 I2 T
          let Q3 := M.stageThreeForcing c.carrier I0 I1 action pres nodes d T T2 next2.valid1
          ∃ hCarrier : pres.carrier ∈ M.sets, ∃ hOrder : pres.conditionOrder ∈ M.sets,
          let tests := M.refinementLevelTests pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1
            action nodes d base directed next2.first (natSetCode 2) T2
          let Condition3 := FlatSuccessorCondition M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
            pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
            hNodes prior.terms_ground next.indices base directed next.first
          let laws := M.stageThreeFlatSuccessorLaws pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1 action nodes d base directed next2.first
            actionData.closure_data.projection_data.first_level next.indices.levelCode next2.indices.levelCode
          letI := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          letI := M.flatSuccessorSmallTop c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
          let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let restriction := M.flatSuccessorSmallRestriction c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2
          let inclusion := M.flatSuccessorSmallInclusion c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
          pres3.carrier = Q3 ∧ pres3.carrier ∈ M.sets ∧
          pres3.conditionOrder = rowAssignmentOrder pres3.carrier c.carrier
            (M.groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega) c.conditionOrder ∧
          pres3.conditionOrder ∈ M.sets ∧ pres3.encode ⊤ = pres.encode ⊤ ∧
          CompleteProjection restriction inclusion ∧
          (∀ q : Shrink Condition, pres3.encode (inclusion q) = pres.encode q) ∧
          (∀ p : Shrink Condition3, pres.encode (restriction p) =
            ZFSet.pair (c.encode ((equivShrink Condition3).symm p).row)
              (assignmentCut levels (natSetCode 2) ((equivShrink Condition3).symm p).assignments)) ∧
          pres3.graph pres restriction = rowAssignmentCutGraph pres3.carrier pres.carrier levels (natSetCode 2) ∧
          pres3.graph pres restriction ∈ M.sets

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageThreeProjectionData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageThreeCarrierData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (rows : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageThreeProjectionData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.name_lifting.support_data.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, next2, hCarrier, hOrder, _⟩ := prior.construction
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first F first second
  let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
  let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first a image inputs
  let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
  let levels := stageThreeAssignmentLevels I0 I1 I2 T
  let tests := M.refinementLevelTests pres pairing unions powers separation collection hCarrier hOrder
    data.terms_ground next2.valid1 action nodes d base directed next2.first (natSetCode 2) T2
  let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    hNodes data.terms_ground next.indices base directed next.first
  let laws := M.stageThreeFlatSuccessorLaws pres pairing unions powers separation collection
    hCarrier hOrder data.terms_ground next2.valid1 action nodes d base directed next2.first
    first second next2.indices.levelCode
  let := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  let := M.flatSuccessorSmallTop c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
  let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  have omega := M.omega_mem separation infinite
  refine ⟨prior, F, hNodes, inputs, next2, hCarrier, hOrder, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.stageThreeFlatPresentation_carrier c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first
  · exact M.stageThreeFlatPresentation_carrier_mem c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first rows hI0 next.indices.index_ground nodeOrder omega
  · exact M.flatSuccessorConditionOrder_eq c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  · exact M.stageThreeFlatOrder_mem c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first rows hI0 next.indices.index_ground rowOrder nodeOrder omega
  · exact M.flatSuccessorPresentation_top c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
  · exact M.flatSuccessorSmallCompleteProjection c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
      pairing unions powers separation infinite choice
      (M.stageThreeAssignmentLevels_mem pairing unions powers separation hI0 next.indices.index_ground
        next2.indices.index_ground data.terms_ground)
      (M.transitive omega (natSetCode_mem_omega 2))
  · exact M.flatSuccessorSmallInclusion_encode c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
  · exact M.flatSuccessorSmallRestriction_encode c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2
  · rw [M.stageThreeFlatPresentation_carrier c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first]
    exact M.stageThreeSmallRestriction_graph c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first F2
  · exact M.stageThreeSmallRestriction_graph_mem c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first F2 rows hI0 next.indices.index_ground nodeOrder omega

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeClosureData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  projection_data : StageThreeProjectionData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  closed :
    let actionData := projection_data.carrier_data.name_lifting.support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
        next.indices.levelCode
      ∃ hNodes : nodes.carrier ∈ M.sets,
      ∃ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first
        let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first a image inputs
        ∃ next2 : RefinementStageSystem M action pres actors nodes d base directed (natSetCode 2) T T2,
          let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
          let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
          let levels := stageThreeAssignmentLevels I0 I1 I2 T
          ∃ hCarrier : pres.carrier ∈ M.sets, ∃ hOrder : pres.conditionOrder ∈ M.sets,
          let tests := M.refinementLevelTests pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1
            action nodes d base directed next2.first (natSetCode 2) T2
          let Condition3 := FlatSuccessorCondition M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
            pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
            hNodes prior.terms_ground next.indices base directed next.first
          letI := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let restriction := M.flatSuccessorSmallRestriction c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2
          InternallyCountablyClosed M pres3 ∧
          (∀ seq : Nat → Shrink Condition3,
            natPresentation.graph pres3 (fun n => seq n.down) ∈ M.sets → Antitone seq →
            ∃ q : Shrink Condition, (∀ n, q ≤ restriction (seq n)) ∧ ∃ p : Shrink Condition3,
              ((equivShrink Condition3).symm p).lower = q ∧
              ((equivShrink Condition3).symm p).assignments =
                assignmentSplice levels (natSetCode 2) (F2.assignments q)
                  (stageOneAssignmentUnion (fun n => ((equivShrink Condition3).symm (seq n)).assignments)) ∧
              ∀ n, p ≤ seq n)

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageThreeClosureData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageThreeProjectionData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageThreeClosureData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.carrier_data.name_lifting.support_data.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, next2, hCarrier, hOrder, _⟩ := prior.projections
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first F first second
  let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
  let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first a image inputs
  let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
  let levels := stageThreeAssignmentLevels I0 I1 I2 T
  let tests := M.refinementLevelTests pres pairing unions powers separation collection hCarrier hOrder
    data.terms_ground next2.valid1 action nodes d base directed next2.first (natSetCode 2) T2
  let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    hNodes data.terms_ground next.indices base directed next.first
  obtain ⟨_, lowerClosed⟩ := actionData.closure_data.closed
  refine ⟨prior, F, hNodes, inputs, next2, hCarrier, hOrder, ?_, ?_⟩
  · exact M.stageThreeCondition_internally_closed c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first F2 first second infinite choice rows hI0
      next.indices.index_ground nodeOrder lowerClosed
  · exact M.stageThreeCondition_lower_bound c I0 I1 action pres nodes d T T2 next2.valid1
      pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
      next2.indices base directed next2.first F2 first second infinite choice rows hI0
      next.indices.index_ground nodeOrder lowerClosed

end TransitiveGround

end PartitionPilot.Forcing

end OAI
