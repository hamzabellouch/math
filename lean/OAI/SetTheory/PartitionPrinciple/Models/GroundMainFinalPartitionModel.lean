import OAI.SetTheory.PartitionPrinciple.Definability.GroundMainFinalGraphValueCandidateAvailability
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralSymmetricRefinementOutputs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalPersistentAssignmentLabels
import OAI.SetTheory.PartitionPrinciple.Models.GroundMainFinalStructuralRowNonchoice
import OAI.SetTheory.PartitionPrinciple.Models.GroundRowCoverPartitionPrinciple
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundExtensionOrdinals
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveOriginalRowFamilies

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)

theorem symmetricExtension_quotient_injections
    (H : ConditionFilter P) (rowName : Name s)
    (named : ∀ tau : Fin 3 → (M.nameDomain s).names,
      (∀ i, HereditarilySymmetric a s F (tau i).val) →
      RefinementValidityCode (Name.eval {p | H.mem p} rowName)
        (Name.eval {p | H.mem p} (tau 0).val)
        (Name.eval {p | H.mem p} (tau 1).val)
        (Name.eval {p | H.mem p} (tau 2).val) →
      ∃ J ∈ (M.symmetricExtension s a F H).sets,
        InjectionCode
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val))
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val)) J) :
    ∀ U ∈ (M.symmetricExtension s a F H).sets,
      ∀ Rf ∈ (M.symmetricExtension s a F H).sets,
        ∀ Rc ∈ (M.symmetricExtension s a F H).sets,
          RefinementValidityCode (Name.eval {p | H.mem p} rowName) U Rf Rc →
            (M.symmetricExtension s a F H).groundEmbeddable
              (equivalenceClasses U Rc) (equivalenceClasses U Rf) := by
  intro U hU Rf hRf Rc hRc validity
  obtain ⟨u, hu, symmetricU, equalU⟩ := (M.mem_symmetricExtension s a F H U).1 hU
  obtain ⟨fine, hFine, symmetricFine, equalFine⟩ := (M.mem_symmetricExtension s a F H Rf).1 hRf
  obtain ⟨coarse, hCoarse, symmetricCoarse, equalCoarse⟩ :=
    (M.mem_symmetricExtension s a F H Rc).1 hRc
  let tau : Fin 3 → (M.nameDomain s).names := ![⟨u, hu⟩, ⟨fine, hFine⟩, ⟨coarse, hCoarse⟩]
  have symmetric : ∀ i, HereditarilySymmetric a s F (tau i).val :=
    Fin.cases symmetricU (Fin.cases symmetricFine (Fin.cases symmetricCoarse (fun i => Fin.elim0 i)))
  have actual : RefinementValidityCode (Name.eval {p | H.mem p} rowName)
      (Name.eval {p | H.mem p} (tau 0).val)
      (Name.eval {p | H.mem p} (tau 1).val)
      (Name.eval {p | H.mem p} (tau 2).val) := by
    change RefinementValidityCode (Name.eval {p | H.mem p} rowName)
      (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} fine) (Name.eval {p | H.mem p} coarse)
    rwa [equalU, equalFine, equalCoarse]
  obtain ⟨J, hJ, injection⟩ := named tau symmetric actual
  refine ⟨J, hJ, ?_⟩
  change InjectionCode
    (equivalenceClasses (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} coarse))
    (equivalenceClasses (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} fine)) J at injection
  rwa [equalU, equalFine, equalCoarse] at injection

end PartitionPilot.Forcing.TransitiveGround




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

theorem structural_ordinal_choice
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ H : ConditionFilter (SetMembers upperQ),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
    ZFRealization N.sets →
      ∀ delta ∈ N.sets, ordinalSetProperty delta →
        ∀ z ∈ N.sets, FunctionGraphOn delta z →
          (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
          ∃ f ∈ N.sets, FunctionGraphOn delta f ∧
            ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ f → x ∈ A := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  intro upperAct upper H ordinary N zf delta hDelta ordinal z hz function nonempty
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have groundDelta : delta ∈ M.sets := M.symmetricExtension_ordinal_mem
    pairing unions powers separation collection upper upperAct
    (a.principalSupportFamily ⊥ directed) H hDelta ordinal
  obtain ⟨zName, groundZ, symmetric, same⟩ :=
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H z).1 hz
  obtain ⟨V, fixedZ⟩ := symmetric.symmetric
  obtain ⟨E, strict⟩ := fulfilled.toFinalFulfillment.decoded_strict_growth V
  let original : (M.nameDomain upper).names := ⟨zName, groundZ⟩
  have candidates := fulfilled.structural_graphValue_candidate_availability
    collection infinite choice labels small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace original V E strict symmetric fixedZ
  let W := M.graphValueCandidateCodes upperAct upper (a.principalFix E) zName
  have groundW : W ∈ M.sets := candidates.1
  have validW : ∀ x ∈ W, IsName upper x := candidates.2.1
  have fixed : ∀ psi : Name upper, psi.val ∈ W →
      a.principalFix E ≤ upperAct.stabilizer upper psi := fun psi member =>
    (candidates.2.2.1 psi member).1
  have children : ∀ psi : Name upper, psi.val ∈ W →
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) psi :=
    fun psi member => (candidates.2.2.1 psi member).2
  apply M.supportedNameFamily_graph_choice upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection choice hQ groundW validW
    (a.principalFix E) ⟨E, le_rfl⟩ fixed children H zf hDelta hz function
  intro beta member
  have groundBeta : beta ∈ M.sets := M.transitive groundDelta member
  obtain ⟨A, edge⟩ := function.total member
  have edgeOriginal : ZFSet.pair beta A ∈ Name.eval {p | H.mem p} original.val := by
    rw [show Name.eval {p | H.mem p} original.val = z from same]
    exact edge
  obtain ⟨psi, candidate, B, betaB, chosen⟩ := candidates.2.2.2 beta groundBeta H ordinary
    ⟨A, edgeOriginal, nonempty beta A edge⟩
  exact ⟨psi, candidate, B, same ▸ betaB, chosen⟩






theorem structural_refinement_quotient_injection
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history)
    (_standard : GroundStandardInaccessible M stages)
    (_smallRows : GroundBelow M c.carrier stages) (_smallLifted : GroundBelow M lifted stages),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
  ∀ (H : ConditionFilter (SetMembers upperSet)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    (∀ (beta : ZFSet.{u}) (member : beta ∈ stages),
      let hBeta := M.transitive hs member
      let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
      let betaSubset := (And.left stagesOrdinal) beta member
      let lowerPacked := graphRestriction beta packed
      let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
        (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation lowerSet
      let projection := M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace beta hBeta betaOrdinal betaSubset infinite choice
      (projection.projectedFilter H).GenericFor (M.codedFamily lower) ∧
      (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower))) →
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) (tau i).val) →
      RefinementValidityCode
        (Name.eval {p | H.mem p} (Name.familySet ⊤ lifted validUpper))
        (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
        (Name.eval {p | H.mem p} (tau 2).val) →
      ∃ J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets,
        InjectionCode
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val))
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val)) J := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace standard smallRows smallLifted
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers stagesOrdinal carrier lifted valid1
  intro H ordinary lowerGeneric tau symmetric originalValid
  have indexed := M.semanticStructuralTrace_refinementOutputs c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh standard trace infinite choice smallRows smallLifted small rfl
    fulfilled.toFinalFulfillment.decoded_strict_growth tau symmetric
  obtain ⟨beta, member, data⟩ := indexed
  let hBeta := M.transitive hs member
  let betaOrdinal := ordinalSetProperty_member stagesOrdinal member
  let betaSubset := (And.left stagesOrdinal) beta member
  let lowerPacked := graphRestriction beta packed
  let lowerSet := M.refinementHistoryForcing c.carrier lifted beta lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted beta lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted beta lowerPacked
    (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation lowerSet
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict betaOrdinal betaSubset) betaOrdinal carrier lifted valid1
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
    pairing unions powers separation collection hG hL supports hh hLifted witnesses
  let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal betaOrdinal betaSubset
    pairing unions powers separation infinite choice hs hPacked hLifted hBeta carrier (c.encode ⊤) topMem topRows mono
  dsimp only at data
  obtain ⟨_env, _names, _last, normalized, _entries, _normalizedLast, _forced, _supported,
    V, E, _baseV, _strict, _fixes, index, _stored, _attained, _fineGround, _coarseGround, _mapGround, values⟩ := data
  have outputValues := values H ordinary (lowerGeneric beta member).1 (lowerGeneric beta member).2 originalValid
  obtain ⟨_same, _objects, fineValues, coarseValues, _naturalMap⟩ := outputValues
  have injection := fulfilled.structural_assignment_label_injection collection infinite choice labels small smallD
    irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace beta member V E (normalized 0) (normalized 1) (normalized 2)
    index H ordinary
  have fineEq : Name.eval {q | H.mem (inc q)}
      (Name.refinementQuotient lifted localValid (normalized 0).val (normalized 1).val) =
      equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val) :=
    fineValues
  have coarseEq : Name.eval {q | H.mem (inc q)}
      (Name.refinementQuotient lifted localValid (normalized 0).val (normalized 2).val) =
      equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 2).val) :=
    coarseValues
  refine ⟨_, injection.2, ?_⟩
  rw [← coarseEq, ← fineEq]
  exact injection.1






theorem exists_rowSemanticQuotientInjectionModel
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
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
        ∃ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
          (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
          (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
          (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
          (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
          (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
          (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau),
          ∃ (history : ZFSet.{u}) (hHistory : history ∈ M.sets)
            (trace : OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) K history),
              let coordinateGround := M.prod_mem pairing unions powers separation
                (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
              let nodeActionGround : a.actionGraph s b ∈ M.sets :=
                geometry.decoded_action_eq.symm ▸ geometry.action_ground
              let nodeOrderGround : s.conditionOrder ∈ M.sets :=
                geometry.decoded_order_eq.symm ▸ geometry.order_ground
              let forcingActionGround := M.internalRowActionGraph_mem a s b columns
                pairing unions powers separation infinite geometry.carrier_ground hColumns
                geometry.actors_ground nodeActionGround
              let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
                geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
              let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
                collection geometry.carrier_ground geometry.actors_ground nodeActionGround
              let topMem := c.encode_mem ⊤
              let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
                intro row member
                obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
                exact (c.pair_mem_conditionOrder p ⊤).2 le_top
              let two := M.natSetCode_mem separation infinite 2
              let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
              let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
              let omega := M.omega_mem separation infinite
              let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history
              let Q := M.refinementHistoryForcing c.carrier lifted K packed
              let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
              let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
              let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
              let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
                pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
              let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
                ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
                (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
                  (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
              letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
              let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
                M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
              let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
                (historyRun).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
              let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
                (historyRun).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
                  hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
              let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
                M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
                  j.property.2.1 j.property.2.2 infinite choice
              let upperPres := SetMembers.presentation Q
              let F := a.principalSupportFamily ⊥ directed
              letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
                historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
              let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
                standard.1.1 carrier lifted valid1
              ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
                H.mem p ∧ H.GenericFor (M.codedFamily upperPres) ∧
                H.GenericFor (formulaFamily (M.nameDomain upperPres)) ∧
                H.GenericFor (formulaFamily ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F)) ∧
                (∀ j : Cuts,
                  ((projections j).projectedFilter H).GenericFor
                    (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))) ∧
                  ((projections j).projectedFilter H).GenericFor
                    (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))))) ∧
                M.sets ⊆ ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q} ∧
                ZFRealization (((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q}) ∧
                (∀ U ∈ M.sets,
                  GroundSequenceReflection M (M.ordinaryExtension upperPres H) U ∧
                  GroundSequenceReflection M (M.symmetricExtension upperPres (upperAction) F H) U) ∧
                (∀ tau : Fin 3 → (M.nameDomain upperPres).names,
                  (∀ i, HereditarilySymmetric upperAction upperPres F (tau i).val) →
                  RefinementValidityCode
                    (Name.eval {q | H.mem q} (Name.familySet ⊤ lifted validUpper))
                    (Name.eval {q | H.mem q} (tau 0).val) (Name.eval {q | H.mem q} (tau 1).val)
                    (Name.eval {q | H.mem q} (tau 2).val) →
                  ∃ J ∈ (M.symmetricExtension upperPres upperAction F H).sets,
                    InjectionCode
                      (equivalenceClasses (Name.eval {q | H.mem q} (tau 0).val)
                        (Name.eval {q | H.mem q} (tau 2).val))
                      (equivalenceClasses (Name.eval {q | H.mem q} (tau 0).val)
                        (Name.eval {q | H.mem q} (tau 1).val)) J) := by
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
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.toFinalFulfillment.exists_rowSemanticStructuralSequenceReflection
    collection infinite choice small hK standard indices
  obtain ⟨mu, hmu, hmuK, cardinal, omegaIncluded, positions, ground, below, valid, data⟩ := original
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    _hGraph, _injection, history, hHistory, trace, _hPacked0, _historyRun0, _witnesses0,
    _P, _order0, _top0, _action0, _code0, _fields0, _witness0, final⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omegaIncluded, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    history, hHistory, trace, ?_⟩
  let coordinateGround := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  let nodeActionGround : a.actionGraph s b ∈ M.sets :=
    geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeOrderGround : s.conditionOrder ∈ M.sets :=
    geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let forcingActionGround := M.internalRowActionGraph_mem a s b columns
    pairing unions powers separation infinite geometry.carrier_ground hColumns
    geometry.actors_ground nodeActionGround
  let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  let topMem := c.encode_mem ⊤
  let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
  let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
  let omega := M.omega_mem separation infinite
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared K history
  let Q := M.refinementHistoryForcing c.carrier lifted K packed
  let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
  let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
    b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
    pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
  let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
  let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
    (historyRun).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
  let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
    (historyRun).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
      hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
  let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
    M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
      j.property.2.1 j.property.2.2 infinite choice
  let upperPres := SetMembers.presentation Q
  let F := a.principalSupportFamily ⊥ directed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
    historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
    standard.1.1 carrier lifted valid1
  have conditions := standard.to_conditions pairing unions powers separation hK
  have nodeSize : GroundBelow M s.carrier K :=
    (run.finalGeometry_below i₀ choice hK standard indices).1
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionSize : GroundBelow M s.nonbottom.carrier K :=
    nodeSize.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  have columnSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have rowSize : GroundBelow M c.carrier K :=
    GroundBelow.binaryRowCarrier pairing unions powers separation hPositions hColumns hK
      conditions positionSize columnSize
  have liftedSize : GroundBelow M lifted K := M.pairEmpty_renamedFamily_below c
    pairing unions powers separation collection carrier ground hK valid below
  obtain ⟨_carrierEq, chosen⟩ := final
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetricGeneric, projectedGeneric, includes, zf, reflection⟩ := chosen p
  refine ⟨H, hp, coded, ordinary, symmetricGeneric, projectedGeneric, includes, zf, reflection, ?_⟩
  intro tau symmetric validity
  apply fulfilled.structural_refinement_quotient_injection collection infinite choice labels small smallD
    irreflexive columns hColumns hmu cardinal.1 valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 K history hK hHistory standard.1.1 trace standard rowSize liftedSize H ordinary
    _ tau symmetric validity
  intro beta member
  exact projectedGeneric ⟨beta, M.transitive hK member,
    ordinalSetProperty_member standard.1.1 member, (And.left standard.1.1) beta member⟩






include fulfilled

theorem exists_partitionPrinciple_not_choice
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      (∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
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
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.exists_rowSemanticQuotientInjectionModel
    collection infinite choice small hK standard indices labels smallD irreflexive
  obtain ⟨mu, hmu, _hmuK, cardinal, _omegaIncluded, positions, _ground, _below, valid, data⟩ := original
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    history, hHistory, trace, chosen⟩ := data
  have topMem := c.encode_mem ⊤
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have omega := M.omega_mem separation infinite
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared K history
  let Q := M.refinementHistoryForcing c.carrier lifted K packed
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
    historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
  let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction geometry.actors_ground
    geometry.carrier_ground nodeOrderGround nodeActionGround nodeMaps supports hLifted hSquared omega
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let upper := SetMembers.presentation Q
  let F := a.principalSupportFamily ⊥ directed
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
    standard.1.1 carrier lifted valid1
  let rowName := Name.familySet (⊤ : SetMembers Q) lifted validUpper
  obtain ⟨H, _atTop, _coded, ordinary, _symmetricGeneric, _projectedGeneric,
    includes, zf, _reflection, named⟩ := chosen (⊤ : SetMembers Q)
  let N := M.symmetricExtension upper upperAction F H
  have quotientInjection := M.symmetricExtension_quotient_injections upper upperAction F H rowName named
  have uncountable : ¬ M.groundEmbeddable columns ZFSet.omega :=
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.2
  have covers := M.semanticBinaryRow_ordinal_partial_cover a s b columns
    pairing unions powers separation collection infinite choice geometry.carrier_ground
    nodeOrderGround hColumns geometry.actors_ground nodeActionGround nodeMaps supports directed
    uncountable mu hmu cardinal.1 positions lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 K history hK hHistory standard.1.1 trace
  obtain ⟨validRows, directValid, covers⟩ := covers
  let directRowName : Name upper := Name.familySet (⊤ : SetMembers Q)
    (Name.renamedFamily upper
      (M.refinementHistoryRowInclusion c historyRun.carriers standard.1.1 carrier) T validRows) directValid
  have actualCover :
      let Trow := Name.eval {p | H.mem p} directRowName
      Trow ∈ N.sets ∧
        ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
          ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
            (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
            ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
              ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := covers H ordinary
  have sameRows : directRowName = rowName :=
    M.refinementHistory_originalRowFamilySet_eq c historyRun.carriers
      standard.1.1 carrier (⊤ : SetMembers Q) T validRows directValid validUpper
  rw [sameRows] at actualCover
  have acwo := fulfilled.structural_ordinal_choice collection infinite choice labels small smallD
    irreflexive columns hColumns hmu cardinal.1 valid hLifted hSquared valid1 valid2 closed1
    closed2 children1 children2 K history hK hHistory standard.1.1 trace H ordinary zf
  have notChoice := fulfilled.structural_lifted_rows_not_wellorderable_not_choice
    collection infinite choice small smallD irreflexive columns hColumns uncountable hmu
    cardinal.1 valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    K history hK hHistory standard.1.1 trace H ordinary zf
  exact ⟨N, includes, zf,
    N.partitionPrinciple_of_rowCover_quotients zf actualCover.1 acwo actualCover.2 quotientInjection,
    notChoice.2.2⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
