import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedAlignedReferenceCollisions
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalPrefixPreparationBatches
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralBirthLevelSelectors

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_preparationTransition
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
    ∀ (pUpper : SetMembers upperQ) (row A : ZFSet.{u})
      (_code : SetMembers.raw pUpper = ZFSet.pair row A),
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    ∀ (_descent : ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val),
      ∃ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) ∧
        H.GenericFor (formulaFamily (M.nameDomain lower)) ∧ H.mem (restriction pUpper) ∧
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
        M.groundEmbeddable J ZFSet.omega ∧
        (∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
          Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
        (∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          j ∈ J ∧ F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          M.groundEmbeddable B ZFSet.omega ∧ F ⊆ b.carrier ∧ B ⊆ F ∧
          (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ geometry.order) ∧
          ZFSet.IsFunc B (M.niceSupportNameCodes lowerAct lower T d.principalFix) f ∧
          ∀ v ∈ B, ∀ tau ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix,
            ZFSet.pair v tau ∈ f →
              ZFSet.pair v tau ∈ M.niceSupportRelation lowerAct lower b T d.principalFix) ∧
        k ⊆ M.supportedCertificateFamilyRelation lowerAct lower b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ restriction pUpper ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) q ∧
          ∃ (r : SetMembers upperQ) (newRow newA : ZFSet.{u}),
            r ≤ pUpper ∧ restriction r = q ∧
            SetMembers.raw r = ZFSet.pair newRow newA ∧
            ZFSet.pair newRow row ∈ c.conditionOrder ∧ A ⊆ newA ∧
            SetMembers.raw (restriction r) = ZFSet.pair newRow
              (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA) ∧
            H.mem (restriction r) ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) (restriction r) ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes lowerAct lower T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile lowerAct lower b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile lowerAct lower b d.principalFix T F z.val (restriction r) ∧
              (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq (restriction r) z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes lowerAct lower T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history alpha hs hh ordinal trace member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let instUpperHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
  let projection := M.semanticStructuralTrace_completeProjection c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset
    infinite choice
  intro pUpper row A code descent
  obtain ⟨H, hp, genericCoded, genericFormula⟩ :=
    M.exists_coded_ordinary_generic lower small lowerGround (restriction pUpper)
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  have condition : ZFSet.pair row A ∈ upperQ := code ▸ SetMembers.raw_mem pUpper
  obtain ⟨validJ, hJ, smallJ, facts, k, hk, function, selectedCertificates,
      q, hq, qp, forced, enumerations, hEnumerations, enumerationFunction,
      enumerationRelation, synchronized, entries⟩ :=
    fulfilled.exists_prefixPreparationBatch c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history alpha hs hh ordinal trace member row A condition
      H genericCoded genericFormula (descent H genericCoded genericFormula) (restriction pUpper) hp
  obtain ⟨r, rp, rq⟩ := projection.lift pUpper q qp
  obtain ⟨newRow, _, newA, _, rCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem r))
  have belowRaw : ZFSet.pair (SetMembers.raw r) (SetMembers.raw pUpper) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := rp
  rw [rCode, code] at belowRaw
  have fields := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    newRow newA row A).1 belowRaw
  have cut := historyRun.restrictionFunction_raw ordinal cutOrdinal subset r newRow newA rCode
  refine ⟨H, genericCoded, genericFormula, hp, validJ, hJ, smallJ, facts, k, hk, function, ?_,
    selectedCertificates, q, hq, qp, forced, r, newRow, newA, rp, rq, rCode,
    fields.2.2.1, fields.2.2.2, cut, rq.symm ▸ hq, rq.symm ▸ forced,
    enumerations, hEnumerations, enumerationFunction, enumerationRelation, synchronized, ?_⟩
  · intro j F B f entry
    exact M.supportedCertificateFamily_groundData lowerAct lower b T d.principalFix
      geometry.order J validJ H j F B f (selectedCertificates entry)
  · intro z F B f stored
    exact rq.symm ▸ entries z F B f stored






theorem exists_groundPreparationSteps
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  let levels := refinementDataHistoryLevels stages packed T
  let relation := M.storedPreparationRelation upperQ
    (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed)
    b.carrier T levels alpha geometry.meetGraph fields
    ∀ (_descent : ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val),
      relation ∈ M.sets ∧ ∃ step ∈ M.sets,
        ZFSet.IsFunc upperQ (M.preparationWitnessBound b.carrier T upperQ) step ∧
        step ⊆ relation := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history alpha hs hh ordinal trace member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let lowerOrder := inputs.2.1
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let instUpperHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
  intro descent
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  let levels := refinementDataHistoryLevels stages packed T
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.storedPreparationRelation upperQ upperOrder b.carrier T levels alpha geometry.meetGraph fields
  have packedGround := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2
        (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
  have fieldGround : ∀ j, fields j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem fields (M.pair_right (M.transitive packedGround stored))
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset
    infinite choice
  have upperOrderGround := M.refinementHistoryOrder_mem pairing unions powers separation
    carrier rowOrder hT hs packedGround omega
  have levelsGround := M.refinementDataHistoryLevels_mem pairing unions powers separation hs packedGround hT
  have meetCode : MeetOrderCode (fields 10) (fields 11) geometry.meetGraph := by
    change MeetOrderCode b.carrier b.conditionOrder geometry.meetGraph
    rw [geometry.decoded_order_eq]
    exact geometry.meet
  have relationGround : relation ∈ M.sets := M.storedPreparationRelation_mem
    pairing unions powers separation bounds.1 upperOrderGround geometry.carrier_ground hT
    levelsGround hAlpha geometry.meet_ground omega fields fieldGround meetCode
  have total : ∀ input ∈ upperQ, ∃ output ∈ M.preparationWitnessBound b.carrier T upperQ,
      ZFSet.pair input output ∈ relation := by
    intro input hInput
    obtain ⟨row, _, A, _, rfl⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier T stages packed hInput)
    let pUpper := SetMembers.ofMem (ZFSet.pair row A) hInput
    have pCode : SetMembers.raw pUpper = ZFSet.pair row A := SetMembers.raw_ofMem _ _
    let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    let selected := assignmentOnIndices indices T A
    let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
    let bound := M.groundRelations T lower.carrier
    let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    obtain ⟨H, _genericCoded, _genericFormula, _hp, validJ, hJ, _smallJ, _facts,
        k, hk, function, _groundData, selectedCertificates, q, _hq, _qp, _forced,
        r, newRow, newA, rp, _rq, rCode, _rowBelow, _retained, cut, _hr, _forcedr,
        enumerations, hEnumerations, enumerationFunction, _enumerationRelation, synchronized, entries⟩ :=
      fulfilled.exists_preparationTransition c collection infinite choice small smallD irreflexive rowClosed
        a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
        topMem topRows stages history alpha hs hh ordinal trace member pUpper row A pCode descent
    have prepared := M.preparedCertificateFamilyCode_of_selected lowerAct lower b T d.principalFix
      pairing unions powers separation collection lowerGround lowerOrder hT valid (fieldGround 13)
      geometry.order geometry.meetGraph J hJ validJ H (restriction r) k enumerations
      function selectedCertificates enumerationFunction synchronized (by
        intro z F B f entry
        have data := entries z F B f entry
        exact ⟨data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2.1⟩)
    have enlarged := prepared.bounds_mono
      (M.supportedEqualityCertificateBound_mono bounds.2.2.2)
      (M.synchronizedEnumerationBound_mono bounds.2.2.2)
    have witnessBound := M.semanticStructuralPreparationWitness_mem c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
      geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
      closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset
      infinite choice A (SetMembers.raw r) k enumerations (SetMembers.raw_mem r) hk hEnumerations
      function enumerationFunction
    refine ⟨ZFSet.pair (SetMembers.raw r) (ZFSet.pair k enumerations), witnessBound, ?_⟩
    apply (M.pair_mem_storedPreparationRelation upperQ upperOrder b.carrier T levels alpha
      geometry.meetGraph fields _ _).2
    refine ⟨hInput, witnessBound, row, A, SetMembers.raw r, k, enumerations,
      SetMembers.raw (restriction r), rfl, rfl, ?_, ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw pUpper) ∈ upperOrder at rp
      exact pCode ▸ rp
    · change ZFSet.pair (SetMembers.raw r) (SetMembers.raw (restriction r)) ∈
        rowAssignmentCutGraph upperQ Q levels alpha
      rw [rCode]
      exact (pair_mem_rowAssignmentCutGraph upperQ Q levels alpha newRow newA _).2
        ⟨rCode ▸ SetMembers.raw_mem r, SetMembers.raw_mem (restriction r), cut⟩
    · change PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder
        (lower.encode (restriction r)) b.carrier b.conditionOrder geometry.meetGraph
        (M.groundRelations T lower.carrier) (M.niceVisibilityGraph lowerAct lower b T d.principalFix)
        (lower.encode ⊤) ZFSet.omega J
        (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
        (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations
      let codeAtOrder := fun orderCode : ZFSet.{u} =>
        PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder
          (lower.encode (restriction r)) b.carrier orderCode geometry.meetGraph
          (M.groundRelations T lower.carrier) (M.niceVisibilityGraph lowerAct lower b T d.principalFix)
          (lower.encode ⊤) ZFSet.omega J
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations
      exact Eq.mpr (congrArg codeAtOrder geometry.decoded_order_eq) enlarged
  obtain ⟨step, ground, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    bounds.1 bounds.2.1 relationGround total
  exact ⟨relationGround, step, ground, function, selected⟩






theorem exists_varyingGroundPreparationSteps
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
      relation ∈ M.sets ∧ ∃ step ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ) (M.preparationWitnessBound b.carrier T upperQ) step ∧
        step ⊆ relation := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
  intro descent
  have packedGround := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2
        (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have upperGround := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs packedGround omega
  have upperOrderGround := M.refinementHistoryOrder_mem pairing unions powers separation
    carrier rowOrder hT hs packedGround omega
  have boundGround := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT upperGround omega
  have inputGround := M.prod_mem pairing unions powers separation hs upperGround
  have relationGround : relation ∈ M.sets := M.varyingPreparationRelation_mem
    pairing unions powers separation hs packedGround upperGround upperOrderGround
    geometry.carrier_ground hT omega
  have total : ∀ input ∈ ZFSet.prod stages upperQ,
      ∃ output ∈ M.preparationWitnessBound b.carrier T upperQ,
        ZFSet.pair input output ∈ relation := by
    intro input hInput
    obtain ⟨alpha, member, p, hp, rfl⟩ := ZFSet.mem_prod.1 hInput
    let hAlpha := M.transitive hs member
    let cutOrdinal := ordinalSetProperty_member ordinal member
    let subset := (And.left ordinal) alpha member
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let lowerPacked := graphRestriction alpha packed
    let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
    let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
      (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
          pairing unions powers separation collection carrier rowOrder rowAction
          geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
          hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
    obtain ⟨_fixedGround, fixedStep, _stepGround, function, selected⟩ :=
      fulfilled.exists_groundPreparationSteps c collection infinite choice small smallD irreflexive rowClosed
        a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
        topMem topRows stages history alpha hs hh ordinal trace member (descent alpha member)
    obtain ⟨y, entry, _unique⟩ := function.2 p hp
    have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
      geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
      closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
    have meetCode : MeetOrderCode (fields 10) (fields 11) geometry.meetGraph := by
      change MeetOrderCode b.carrier b.conditionOrder geometry.meetGraph
      rw [geometry.decoded_order_eq]
      exact geometry.meet
    exact ⟨y, hy, M.varyingPreparationRelation_of_stored stages packed upperQ upperOrder b.carrier T
      alpha p y geometry.meetGraph fields member stored rfl rfl meetCode (selected entry)⟩
  obtain ⟨step, ground, function, selected⟩ := M.uniformize_relation pairing unions powers separation
    choice inputGround boundGround relationGround total
  exact ⟨relationGround, step, ground, function, selected⟩






theorem exists_groundFairPreparationOrbit
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
    ∀ p ∈ upperQ,
      ∃ enumSelector ∈ M.sets,
        ZFSet.IsFunc upperQ (M.groundRelations ZFSet.omega stages) enumSelector ∧
        enumSelector ⊆ M.birthLevelEnumerationRelation upperQ stages
          (refinementDataHistoryLevels stages packed T) ∧
      ∃ E0 ∈ M.sets, ZFSet.IsFunc upperQ E0 enumSelector ∧
      ∃ prepSelector ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ)
          (M.preparationWitnessBound b.carrier T upperQ) prepSelector ∧
        prepSelector ⊆ relation ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ∃ orbit ∈ M.sets,
        ZFSet.IsFunc ZFSet.omega
          (M.fairPreparationStates upperQ stages (M.preparationWitnessBound b.carrier T upperQ)
            E0 enumSelector) orbit ∧
        (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
          state = ZFSet.pair ∅ (ZFSet.pair p (ZFSet.pair {ZFSet.pair ∅ e} ∅))) ∧
        ∀ n ∈ ZFSet.omega, ∀ state next,
          ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
          FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T upperQ)
            enumSelector prepSelector
            (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
            state next := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
  intro descent p hp
  obtain ⟨_relationGround, prepSelector, hPrep, prepFunction, prepSelected⟩ :=
    fulfilled.exists_varyingGroundPreparationSteps c collection infinite choice small smallD
      irreflexive rowClosed a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2
      closed1 closed2 children1 children2 topMem topRows stages history hs hh ordinal trace descent
  obtain ⟨hQ, _enumBoundGround, _birthRelationGround, enumSelector, hEnum,
      enumFunction, enumSelected, _birthCodes⟩ :=
    M.structuralForcingTrace_birthLevelEnumerations c.carrier c.conditionOrder rowTop
      (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation collection
      infinite choice carrier geometry.actors_ground geometry.carrier_ground nodeOrder supports
      hT hT2 hs hh ordinal trace
  let E0 := relationImage upperQ (M.groundRelations ZFSet.omega stages) enumSelector
  obtain ⟨hE0, _rangeBound, enumCases, _rangeEntries⟩ :=
    M.birthEnumerationRange_spec pairing unions powers separation hQ hs omega
      hEnum enumFunction enumSelected
  have rangeFunction : ZFSet.IsFunc upperQ E0 enumSelector := by
    refine ⟨?_, enumFunction.2⟩
    intro z member
    obtain ⟨q, hq, e, he, rfl⟩ := ZFSet.mem_prod.1 (enumFunction.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hq, (mem_relationImage _ _ _ e).2 ⟨he, q, hq, member⟩⟩
  have hU := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT hQ omega
  have outputShape : ∀ y ∈ M.preparationWitnessBound b.carrier T upperQ,
      ∃ q ∈ upperQ, ∃ payload, y = ZFSet.pair q payload := by
    intro y hy
    obtain ⟨q, hq, payload, _, equal⟩ := ZFSet.mem_prod.1 hy
    exact ⟨q, hq, payload, equal⟩
  obtain ⟨_statesGround, _transitionGround, e, he, chosen, orbit, hOrbit,
      orbitFunction, initial, steps⟩ :=
    M.exists_groundFairPreparationOrbit pairing unions powers separation infinite choice
      hQ hs hU hE0 hEnum hPrep rangeFunction enumCases prepFunction outputShape hp
  refine ⟨enumSelector, hEnum, enumFunction, enumSelected, E0, hE0, rangeFunction,
    prepSelector, hPrep, prepFunction, prepSelected, e, he, chosen,
    orbit, hOrbit, orbitFunction, initial, ?_⟩
  intro n hn state next first second
  exact (steps n hn state next first second).2

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
