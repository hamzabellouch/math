import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAbsentLiftActors
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAssignmentLabelInjectionPackages
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticRepresentedDomainLiftDecisions
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticRepresentedDomainPersistence
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalPrefixCompatibleCaps
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalSuccessorPreparedProfiles

namespace OAI

open scoped ZFSet



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

theorem structural_successor_represented_of_nonvisible
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ pCut r0 : SetMembers Q,
      let next := graphRestriction (insert alpha alpha) packed
      let upper := M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) next
      let levels := refinementDataHistoryLevels (insert alpha alpha) next lifted
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r0 ≤ pCut →
      Name.ForcesMem r0 u.val U.val →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ lifted → z.val.val ∈ lifted →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ r0 → ¬ Name.ForcesEq q
          (Name.refinementClass lifted localValid Rc.val u.val)
          (Name.refinementClass lifted localValid Rc.val v.val)) →
      (∀ q, q ≤ r0 → ¬ Name.ForcesMem q
        (Name.refinementClass lifted localValid Rf.val u.val)
        (M.niceVisibilityName localAct lower lifted (a.principalFix V))) →
      ∃ newRow newA : ZFSet.{u},
        ZFSet.pair newRow newA ∈
          M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u ∧
        ZFSet.pair (ZFSet.pair newRow newA) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted (insert alpha alpha) next ∧
        A ⊆ newA := by
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
    stages history hs hh stagesOrdinal trace
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
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
  intro row A condition V E U Rf Rc u inI hu pCut r0 cutCode r0p active fresh absent
  let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
  let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
  let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
  obtain ⟨_hJ, _smallJ, k, _hk, _function, profilesGround, profilesSmall, profileFilters,
    Pb, _basis, _representatives, _coarseEntry, pbMember,
    generators, hGenerators, _smallGenerators, generatorsNonempty, generatorsSubset, generatedEq,
    r, rr0, rowR, lowerA, rCode, prepared,
    D0, eD0, uSupport, rowsBound, dataBound, coarseDecisions, _allDecisions, oldProfiles⟩ :=
    fulfilled.successor_prepared_insertion_profiles collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      row A condition V E U Rf Rc u inI hu r0
  let system := M.semanticStructuralPrefix_refinementSystem c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member
  have strict := ((system.indices.typed_entries V E U Rf Rc).1 inI).1
  have vD0 := strict.le.trans eD0
  obtain ⟨g, cap, q, qr, qgr, fixed, _above, _notAbove, movedBound,
    capPositive, capNegative, avoidProfiles, _unionCoordinates⟩ :=
    fulfilled.structural_prefix_compatible_caps collection infinite choice labels small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      r rowR lowerA rCode prepared V E D0 generators Pb (M.certificateProfileImage J s.carrier N k)
      strict vD0 (profileFilters Pb pbMember) hGenerators generatorsNonempty generatorsSubset
      generatedEq profilesGround profilesSmall profileFilters rowsBound dataBound
  have descent := fulfilled.structural_prefix_descent collection infinite choice small smallD irreflexive
    columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace alpha member
  obtain ⟨w, _acted, _hw, _activeW, _groundD, newRow, newLowerA, _qCode,
    _upperMember, edge, retained, _newAssignment, _cut, _self, inD⟩ :=
    M.semanticStructuralSuccessor_represented_absentLift_actor c act b s a ⊥ directed
      lifted squared (c.encode ⊤) pairing unions powers separation collection
      carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega
      valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace member
      infinite choice small condition geometry.meet.smallMeet descent
      V E D0 cap U Rf Rc u Pb inI hu vD0 uSupport g fixed movedBound
      pCut r q cutCode (rr0.trans r0p) qr qgr (Name.forcesMem_mono active rr0)
      capPositive capNegative coarseDecisions
      (fun p pr => absent p (pr.trans rr0))
      (by
        intro v z hv hz old
        obtain ⟨F, _B, _f, _entry, memberF, decisions⟩ := oldProfiles v z hv hz old
        exact ⟨fun p pr => fresh v z hv hz old p (pr.trans rr0),
          F, decisions, avoidProfiles F memberF⟩)
  exact ⟨newRow, _, inD, edge, retained⟩






theorem structural_represented_domain_dense
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      let next := graphRestriction (insert alpha alpha) packed
      let upper := M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) next
      let levels := refinementDataHistoryLevels (insert alpha alpha) next lifted
      let Dt := M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u
      Dt ∈ M.sets ∧ Dt ⊆ upper ∧
        (∀ p q, ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder lifted
          (insert alpha alpha) next → p ∈ Dt → q ∈ Dt) ∧
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted (insert alpha alpha) next
        Dense {p : SetMembers upper | SetMembers.raw p ∈ Dt} := by
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
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid
  let gamma := insert alpha alpha
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  let historyGamma := graphRestriction gamma history
  have hhGamma : historyGamma ∈ M.sets := M.graphRestriction_mem unions separation hGamma hh
  have traceGamma := trace.restrict gammaOrdinal gammaSubset
  let packedGamma := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared gamma historyGamma
  have packedGammaEq : packedGamma = graphRestriction gamma packed :=
    (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared gamma history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared gammaSubset)
  let next := graphRestriction gamma packed
  let upper := M.refinementHistoryForcing c.carrier lifted gamma next
  let levels := refinementDataHistoryLevels gamma next lifted
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder lifted gamma next
  let Property : ∀ (domainSet : ZFSet.{u}) (orderQ : PartialOrder (SetMembers domainSet)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers domainSet) orderQ → Prop :=
    fun domainSet orderQ actionQ =>
      letI := orderQ
      ∀ topQ : OrderTop (SetMembers domainSet),
      letI := topQ
      let lower := SetMembers.presentation domainSet
      ∀ localValid : ∀ z ∈ lifted, IsName lower z,
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices actionQ lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      let Dt := M.representedDomainConditions lower upper levels alpha lifted localValid idx U Rc u
      Dt ∈ M.sets ∧ Dt ⊆ upper ∧
        (∀ p q, ZFSet.pair q p ∈ upperOrder → p ∈ Dt → q ∈ Dt) ∧
        ∀ p ∈ upper, ∃ q ∈ Dt, ZFSet.pair q p ∈ upperOrder
  let QGamma := M.refinementHistoryForcing c.carrier lifted alpha (graphRestriction alpha packedGamma)
  let gammaOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma)
  let runGamma := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared gammaOrdinal traceGamma
  let topGamma := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma) (runGamma.carriers.restrict cutOrdinal alphaGamma)
    cutOrdinal carrier (c.encode ⊤) topMem topRows
  let validGamma := M.refinementHistoryRowNameFamily_valid c
    (runGamma.carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier lifted valid1
  let actionGamma := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma
  have inside : Property QGamma gammaOrder actionGamma := by
    intro topQ
    have topEq : topQ = topGamma := Subsingleton.elim _ _
    subst topQ
    dsimp only
    intro validQ
    have validEq : validQ = validGamma := Subsingleton.elim _ _
    subst validQ
    intro V E U Rf Rc u inI hu
    let lowerGamma := SetMembers.presentation QGamma
    let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
    let upperGamma := M.refinementHistoryForcing c.carrier lifted gamma packedGamma
    let levelsGamma := refinementDataHistoryLevels gamma packedGamma lifted
    let orderGamma := M.refinementHistoryOrder c.carrier c.conditionOrder lifted gamma packedGamma
    have upperEq : upperGamma = upper := by dsimp only [upperGamma, upper, next]; rw [packedGammaEq]
    have levelsEq : levelsGamma = levels := by dsimp only [levelsGamma, levels, next]; rw [packedGammaEq]
    have orderEq : orderGamma = upperOrder := by dsimp only [orderGamma, upperOrder, next]; rw [packedGammaEq]
    let DtGamma := M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u
    let DtOuter := M.representedDomainConditions lowerGamma upper levels alpha lifted validGamma idx U Rc u
    have domainEq : DtGamma = DtOuter := by
      dsimp only [DtGamma, DtOuter]
      rw [upperEq, levelsEq]
    have moveMember {z : ZFSet.{u}} (h : z ∈ DtGamma) : z ∈ DtOuter :=
      Eq.mp (congrArg (fun bound : ZFSet.{u} => z ∈ bound) domainEq) h
    have moveOrder {z p : ZFSet.{u}} (h : ZFSet.pair z p ∈ orderGamma) :
        ZFSet.pair z p ∈ upperOrder :=
      Eq.mp (congrArg (fun relation : ZFSet.{u} => ZFSet.pair z p ∈ relation) orderEq) h
    have selfRestrict : graphRestriction gamma packedGamma = packedGamma :=
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared (fun _ h => h : gamma ⊆ gamma)).symm
    have hIdx := M.refinementIndexCode_mem pairing hAlpha
      (M.transitive hL (s.encode_mem V)) (M.transitive hL (s.encode_mem E))
      U.property Rf.property Rc.property
    obtain ⟨groundD, subsetD, downwardD⟩ :=
      M.semanticStructuralPrefix_representedDomain_ground_downward c act b s a ⊥ directed lifted squared
        (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
        hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
        children1 children2 topMem topRows hGamma hhGamma gammaOrdinal traceGamma
        (ZFSet.mem_insert alpha alpha) idx hIdx U Rc u
    change M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u ∈ M.sets at groundD
    change M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u ⊆ upperGamma at subsetD
    change ∀ p q, ZFSet.pair q p ∈ orderGamma →
      p ∈ M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u →
      q ∈ M.representedDomainConditions lowerGamma upperGamma levelsGamma alpha lifted validGamma idx U Rc u at downwardD
    rw [upperEq, levelsEq] at groundD subsetD
    rw [upperEq, levelsEq, orderEq] at downwardD
    refine ⟨groundD, subsetD, downwardD, ?_⟩
    intro p hp
    have hpGamma : p ∈ upperGamma := upperEq.symm ▸ hp
    obtain ⟨row, _rowMem, A, _assignmentsMem, pCode⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier lifted gamma packedGamma hpGamma)
    subst p
    obtain ⟨pCut, r, cutCode, below, lowerRow, lowerA, _rCode,
      _liftedCondition, liftedBelow, _retained, _exactCut, represented | fresh⟩ :=
      M.semanticStructuralSuccessor_represented_or_fresh b s a ⊥ directed
        pairing unions powers separation collection infinite choice
        (ZFSet.prod s.nonbottom.carrier columns) coordinates act lifted squared (c.encode ⊤)
        forcingAction hG hL order graph nodeMaps supports hLifted hSquared
        valid1 valid2 closed1 closed2 children1 children2 topMem topRows
        gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma alpha (ZFSet.mem_insert alpha alpha)
        hpGamma V E U Rf Rc inI u.val hu
    · exact ⟨ZFSet.pair lowerRow (assignmentSplice levelsGamma alpha lowerA A),
        moveMember represented, moveOrder liftedBelow⟩
    · obtain ⟨active, coarseFresh⟩ := fresh
      have successorCondition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted
          (insert alpha alpha) (graphRestriction (insert alpha alpha) packedGamma) := by
        change ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted gamma (graphRestriction gamma packedGamma)
        rw [selfRestrict]
        exact hpGamma
      have successorCut : lowerGamma.encode pCut = ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels (insert alpha alpha)
            (graphRestriction (insert alpha alpha) packedGamma) lifted) alpha A) := by
        change lowerGamma.encode pCut = ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels gamma (graphRestriction gamma packedGamma) lifted) alpha A)
        rw [selfRestrict]
        exact cutCode
      obtain ⟨q, qr, activeQ, freshQ, positive | negative⟩ :=
        M.semanticStructuralSuccessor_decide_represented_visibleLift c act b s a ⊥ directed lifted squared
          (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
          hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
          children1 children2 topMem topRows hGamma hhGamma gammaOrdinal traceGamma
          (ZFSet.mem_insert alpha alpha) infinite choice small successorCondition
          V E U Rf Rc u inI hu pCut r successorCut below active
          (fun v z hv hz old k kr => coarseFresh v.val z.val hv hz old k kr)
      · obtain ⟨_existsLift, _w, _hw, _activeU, _activeW, newRow, newA, _qCode,
          _newCondition, newBelow, _retained, _literal, _exactCut, _selfEqual, inD⟩ := positive
        rw [selfRestrict] at inD newBelow
        exact ⟨_, moveMember inD, moveOrder newBelow⟩
      · obtain ⟨_absentLift, _fineMember, _mapEdge, nonvisible⟩ := negative
        obtain ⟨newRow, newA, inD, newBelow, _retained⟩ :=
          fulfilled.structural_successor_represented_of_nonvisible collection infinite choice labels
            small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
            valid1 valid2 closed1 closed2 children1 children2
            gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma alpha (ZFSet.mem_insert alpha alpha)
            row A successorCondition V E U Rf Rc u inI hu pCut q successorCut (qr.trans below)
            activeQ freshQ nonvisible
        rw [selfRestrict] at inD newBelow
        exact ⟨ZFSet.pair newRow newA, moveMember inD, moveOrder newBelow⟩
  have outside := (M.semanticStructuralPrefixAction_subhistory_property c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset hGamma gammaOrdinal alphaGamma gammaSubset Property).1 inside
  intro V E U Rf Rc u indexCode inI hu nextOuter upperOuter levelsOuter domainOuter
  obtain ⟨groundD, subsetD, downwardD, denseD⟩ := outside inferInstance localValid V E U Rf Rc u inI hu
  refine ⟨groundD, subsetD, downwardD, ?_⟩
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted gamma next
  intro p
  obtain ⟨q, hq, below⟩ := denseD (SetMembers.raw p) (SetMembers.raw_mem p)
  let qTyped : SetMembers upper := SetMembers.ofMem q (subsetD hq)
  have qCode : SetMembers.raw qTyped = q := SetMembers.raw_ofMem _ _
  refine ⟨qTyped, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw qTyped) (SetMembers.raw p) ∈ upperOrder
    rwa [qCode]
  · change SetMembers.raw qTyped ∈ M.representedDomainConditions lower upper levels alpha lifted
      localValid (refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val) U Rc u
    rw [qCode]
    exact hq






theorem structural_successor_assignment_label_total
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
        historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
      let upper := SetMembers.presentation upperSet
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
      let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
        pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
        topMem topRows mono
      ∀ (_successor : insert alpha alpha = stages)
        (V E : SetMembers geometry.carrier) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid →
      ∀ (H : ConditionFilter (SetMembers upperSet)), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      ∀ z ∈ Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rc.val),
        ∃ y : ZFSet.{u}, ZFSet.pair z y ∈ Name.eval {p | H.mem p}
          (Name.refinementAssignmentLabel upper inc ⊤ lifted localValid idx Rf.val Rc.val) := by
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
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid upperSet
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  intro upper hPacked witnesses mono inc successor V E U Rf Rc indexCode index H ordinary
  apply M.semanticStructuralAssignmentLabel_domain_total c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index H ordinary
  intro u hu
  have result := fulfilled.structural_represented_domain_dense collection infinite choice labels
    small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace alpha member V E U Rf Rc u index hu
  have selfRestrict : graphRestriction stages packed = packed :=
    (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared (fun _ h => h : stages ⊆ stages)).symm
  let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
  change M.representedDomainConditions lower
    (M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed))
    (refinementDataHistoryLevels (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) lifted)
    alpha lifted localValid idx U Rc u ∈ M.sets ∧ _ at result
  let Property : ZFSet.{u} → ZFSet.{u} → Prop := fun nextStage nextPacked =>
    let nextCarrier := M.refinementHistoryForcing c.carrier lifted nextStage nextPacked
    let nextLevels := refinementDataHistoryLevels nextStage nextPacked lifted
    let domain := M.representedDomainConditions lower nextCarrier nextLevels
      alpha lifted localValid idx U Rc u
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted nextStage nextPacked
    domain ∈ M.sets ∧ Dense {p : SetMembers nextCarrier | SetMembers.raw p ∈ domain}
  have packedNext : graphRestriction (insert alpha alpha) packed = packed :=
    (congrArg (fun nextStage => graphRestriction nextStage packed) successor).trans selfRestrict
  exact (congrArg₂ Property successor packedNext).mp ⟨result.1, result.2.2.2⟩






theorem structural_assignment_label_injection
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
        historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
      let upper := SetMembers.presentation upperSet
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
      let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
        pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
        topMem topRows mono
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid →
      ∀ (H : ConditionFilter (SetMembers upperSet)), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let label := Name.refinementAssignmentLabel upper inc ⊤ lifted localValid idx Rf.val Rc.val
      let J := Name.eval {p | H.mem p} label
      let coarse := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rc.val)
      let fine := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rf.val)
      let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace
      InjectionCode coarse fine J ∧
        J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets := by
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
    stages history hs hh stagesOrdinal trace
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
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
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
  let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
    pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
    topMem topRows mono
  intro V E U Rf Rc index H ordinary
  have density := M.semanticStructuralPrefix_representedDomain_persistent_dense c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace member
    infinite choice V E U Rf Rc index (by
      intro u hu
      have successorDensity := fulfilled.structural_represented_domain_dense collection infinite choice labels
        small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
        valid1 valid2 closed1 closed2 children1 children2
        stages history hs hh stagesOrdinal trace alpha member V E U Rf Rc u index hu
      exact ⟨successorDensity.1, successorDensity.2.2.2⟩)
  have total := M.semanticStructuralAssignmentLabel_domain_total c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index H ordinary density
  exact M.semanticStructuralAssignmentLabel_injection_package c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index H ordinary total

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
