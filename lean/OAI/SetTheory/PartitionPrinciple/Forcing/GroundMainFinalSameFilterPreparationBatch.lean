import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralFilterLifts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalPrefixPreparationBatches

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

theorem exists_sameFilterPreparationBatch
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
  let projection := M.semanticStructuralTrace_completeProjection c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset
    infinite choice
    ∀ (Hupper : ConditionFilter (SetMembers upperQ)) (pUpper : SetMembers upperQ)
      (_hpUpper : Hupper.mem pUpper) (row A : ZFSet.{u})
      (_code : SetMembers.raw pUpper = ZFSet.pair row A),
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  let H := projection.projectedFilter Hupper
    ∀ (_genericCoded : H.GenericFor (M.codedFamily lower))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain lower)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val),
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
        M.groundEmbeddable J ZFSet.omega ∧
        (∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
          Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
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
            Hupper.mem r ∧ r ≤ pUpper ∧ restriction r ≤ q ∧
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
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
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
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
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
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let restriction := historyRun.restriction ordinal cutOrdinal subset c.conditionOrder_code
  let projection := M.semanticStructuralTrace_completeProjection c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
    geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset
    infinite choice
  intro Hupper pUpper hpUpper row A code
  let H := projection.projectedFilter Hupper
  intro genericCoded genericFormula descent
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  have condition : ZFSet.pair row A ∈ upperQ := code ▸ SetMembers.raw_mem pUpper
  have hp : H.mem (restriction pUpper) :=
    (projection.projectedFilter_mem_iff Hupper (restriction pUpper)).2 ⟨pUpper, hpUpper, rfl⟩
  obtain ⟨validJ, hJ, smallJ, facts, k, hk, function, selectedCertificates,
      q, hq, qp, forced, enumerations, hEnumerations, enumerationFunction,
      enumerationRelation, synchronized, entries⟩ :=
    fulfilled.exists_prefixPreparationBatch c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history alpha hs hh ordinal trace member row A condition
      H genericCoded genericFormula descent (restriction pUpper) hp
  obtain ⟨r, newRow, newA, hr, rp, rq, rCode, rowBelow, retained, cut⟩ :=
    M.semanticStructuralTrace_sameFilter_lift c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction geometry.actors_ground
      geometry.carrier_ground nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
      closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset
      infinite choice Hupper pUpper hpUpper q hq row A code
  have projectedMember : H.mem (restriction r) :=
    (projection.projectedFilter_mem_iff Hupper (restriction r)).2 ⟨r, hr, rfl⟩
  have strengthened := forces_mono (M.nameDomain lower) supportedCertificateFamilyFormula _ forced rq
  refine ⟨validJ, hJ, smallJ, facts, k, hk, function, selectedCertificates,
    q, hq, qp, forced, r, newRow, newA, hr, rp, rq, rCode, rowBelow, retained, cut,
    projectedMember, strengthened, enumerations, hEnumerations, enumerationFunction,
    enumerationRelation, synchronized, ?_⟩
  intro z F B f stored
  obtain ⟨profile, filter, nonempty, decisions, equalities, perBasis⟩ := entries z F B f stored
  refine ⟨profile, filter, nonempty, ?_, ?_, perBasis⟩
  · intro v
    exact ⟨fun hv => Name.forcesMem_mono ((decisions v).1 hv) rq,
      fun hv stronger below => (decisions v).2 hv stronger (le_trans below rq)⟩
  · intro v hv tau ht edge
    exact Name.forcesEq_mono (equalities v hv tau ht edge) rq

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
