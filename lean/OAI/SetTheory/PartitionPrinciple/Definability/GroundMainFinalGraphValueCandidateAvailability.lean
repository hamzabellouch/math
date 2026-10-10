import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalCompressedNameForcing

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def graphValueCandidateCodes (K : Subgroup G) (tau : Name s) : ZFSet.{u} :=
  Name.supportedFamilyCodes a s K
    (a.orbitCodes s (M.nameDomain s) (Name.descendantFamilyCodes s tau 4))

theorem mem_graphValueCandidateCodes (K : Subgroup G) (tau psi : Name s) :
    psi.val ∈ M.graphValueCandidateCodes a s K tau ↔
      (∃ g : G, ∃ sigma : Name s, sigma.val ∈ M.sets ∧
        sigma.val ∈ Name.descendantFamilyCodes s tau 4 ∧ psi.val = (a.act s g sigma).val) ∧
      K ≤ a.stabilizer s psi := by
  rw [graphValueCandidateCodes, Name.mem_supportedFamilyCodes, a.mem_orbitCodes]
  rfl

theorem graphValueCandidateCodes_hs (F : NormalSubgroupFamily G)
    (K : Subgroup G) (tau : Name s) (symmetric : HereditarilySymmetric a s F tau)
    (psi : Name s) (member : psi.val ∈ M.graphValueCandidateCodes a s K tau) :
    HereditarilySymmetric a s F psi := by
  obtain ⟨⟨g, sigma, _ground, child, equal⟩, _fixed⟩ :=
    (M.mem_graphValueCandidateCodes a s K tau psi).1 member
  have same : psi = a.act s g sigma := Subtype.ext equal
  exact same.symm ▸ (Name.descendantFamilyCodes_hs s a F tau symmetric 4 sigma child).translated g

theorem translated_descendant_mem_graphValueCandidates
    (K : Subgroup G) (tau sigma : Name s) (ground : sigma.val ∈ M.sets)
    (child : sigma.val ∈ Name.descendantFamilyCodes s tau 4)
    (g : G) (fixed : K ≤ a.stabilizer s (a.act s g sigma)) :
    (a.act s g sigma).val ∈ M.graphValueCandidateCodes a s K tau :=
  (M.mem_graphValueCandidateCodes a s K tau _).2 ⟨⟨g, sigma, ground, child, rfl⟩, fixed⟩

theorem graphValueCandidateCodes_mem {I : Type u}
    (t : Presentation G) (b : Presentation I) (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets) (tau : Name s) (ground : tau.val ∈ M.sets) :
    M.graphValueCandidateCodes a s (K i) tau ∈ M.sets := by
  have descendants := M.descendantFamilyCodes_mem s pairing unions powers separation carrier tau ground 4
  have orbit := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps _ descendants
  apply M.supportedFamilyCodes_mem a s t b K pairing unions powers separation collection
    carrier group supports maps i hi _ orbit
  intro z member
  obtain ⟨g, sigma, _ground, _child, rfl⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.descendantFamilyCodes s tau 4) z).1 member
  exact (a.act s g sigma).property

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def GraphValueCandidateDensity (M : TransitiveGround.{u})
    {G P : Type u} [Group G] [PartialOrder P] (action : PosetAction G P)
    (presentation : Presentation P) (support : Subgroup G)
    (z beta : (M.nameDomain presentation).names) (base : P) : Prop :=
  DenseBelow base {q | ∃ tau : (M.nameDomain presentation).names,
    tau.val.val ∈ M.graphValueCandidateCodes action presentation support z.val ∧
    Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend tau (extend z (extend beta Fin.elim0))) q}

theorem graphValueCandidateDensity_of_compression (M : TransitiveGround.{u})
    {G P : Type u} [Group G] [PartialOrder P] (action : PosetAction G P)
    (presentation : Presentation P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)
    (lowerSupport upperSupport : Subgroup G) (prepared : P → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.sets.Countable) (carrier : presentation.carrier ∈ M.sets)
    (z beta : (M.nameDomain presentation).names) (base : P)
    (symmetric : HereditarilySymmetric action presentation F z.val)
    (forced : Forces (M.nameDomain presentation)
      (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base)
    (compress : ∀ tau : (M.nameDomain presentation).names,
      HereditarilySymmetric action presentation F tau.val →
      ∀ p, Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
        (extend tau (extend z (extend beta Fin.elim0))) p →
      ∃ g : G, g ∈ lowerSupport ∧ ∃ sigma : (M.nameDomain presentation).names,
        sigma.val = action.act presentation g tau.val ∧
        HereditarilySymmetric action presentation F sigma.val ∧
        upperSupport ≤ action.stabilizer presentation sigma.val ∧
        ∃ r q : P, r ≤ p ∧ prepared r ∧ q ≤ r ∧ q ≤ action.iso g r ∧
          q ≤ p ∧ q ≤ action.iso g p ∧
          Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
            (extend sigma (extend z (extend beta Fin.elim0))) q) :
    GraphValueCandidateDensity M action presentation upperSupport z beta base := by
  have descendants := M.graphValue_fourthDescendant_dense presentation pairing unions powers separation
    small carrier z beta base forced
  intro p below
  obtain ⟨q, qp, tau, child, witness⟩ := descendants p below
  have hsTau := Name.descendantFamilyCodes_hs presentation action F z.val symmetric 4 tau.val child
  obtain ⟨g, _fixed, sigma, same, _hsSigma, supported,
      _prepared, common, _below, _preparedCode, _toPrepared, _toMovedPrepared,
      toQ, _toMovedQ, recorded⟩ := compress tau hsTau q witness
  have candidate : sigma.val.val ∈ M.graphValueCandidateCodes action presentation upperSupport z.val := by
    apply (M.mem_graphValueCandidateCodes action presentation upperSupport z.val sigma.val).2
    exact ⟨⟨g, tau.val, tau.property, child, congrArg Subtype.val same⟩, supported⟩
  exact ⟨common, toQ.trans qp, sigma, candidate, recorded⟩

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_graphValue_candidates_dense
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
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (z beta : (M.nameDomain upper).names) (V E : SetMembers geometry.carrier)
    (base : SetMembers upperQ), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z.val →
    a.principalFix V ≤ upperAct.stabilizer upper z.val →
    a.principalFix V ≤ upperAct.stabilizer upper beta.val →
    Forces (M.nameDomain upper) (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base →
    GraphValueCandidateDensity M upperAct upper (a.principalFix E) z beta base := by
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
  intro upperAct upper z beta V E base strict symmetric fixedZ fixedBeta forced
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  exact graphValueCandidateDensity_of_compression M upperAct upper
    (a.principalSupportFamily ⊥ directed) (a.principalFix V) (a.principalFix E)
    (fun r : SetMembers upperQ => StoredPreparedConditionCode M c.carrier lifted stages packed
      s.carrier (SetMembers.raw r)) pairing unions powers separation small hQ z beta base symmetric forced
    (fun tau hsTau p witness => fulfilled.structural_compressed_name_forcing
      collection infinite choice labels small smallD irreflexive columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula tau
      (extend z (extend beta Fin.elim0)) V E p strict hsTau
      (Fin.cases fixedZ (Fin.cases fixedBeta (fun j => Fin.elim0 j))) witness)

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




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

theorem structural_graphValue_candidate_availability
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
  ∀ (z : (M.nameDomain upper).names) (V E : SetMembers geometry.carrier), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z.val →
    a.principalFix V ≤ upperAct.stabilizer upper z.val →
    let W := M.graphValueCandidateCodes upperAct upper (a.principalFix E) z.val
    W ∈ M.sets ∧ (∀ x ∈ W, IsName upper x) ∧
      (∀ psi : Name upper, psi.val ∈ W →
        a.principalFix E ≤ upperAct.stabilizer upper psi ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) psi) ∧
      ∀ beta ∈ M.sets, ∀ H : ConditionFilter (SetMembers upperQ),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        (∃ A, ZFSet.pair beta A ∈ Name.eval {p | H.mem p} z.val ∧ A.Nonempty) →
        ∃ psi : Name upper, psi.val ∈ W ∧
          ∃ A, ZFSet.pair beta A ∈ Name.eval {p | H.mem p} z.val ∧
            Name.eval {p | H.mem p} psi ∈ A := by
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
  intro upperAct upper z V E strict symmetric fixedZ W
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hLifted hSquared hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have groundW : W ∈ M.sets := M.graphValueCandidateCodes_mem upperAct upper b s a.principalFix
    pairing unions powers separation collection hQ hG supports maps E
    (M.transitive hL (s.encode_mem E)) z.val z.property
  have validW : ∀ x ∈ W, IsName upper x := by
    intro x member
    dsimp only [W, TransitiveGround.graphValueCandidateCodes, Name.supportedFamilyCodes] at member
    rw [ZFSet.mem_sep] at member
    obtain ⟨psi, same, _fixed⟩ := member.2
    exact same ▸ psi.property
  refine ⟨groundW, validW, ?_, ?_⟩
  · intro psi member
    exact ⟨((M.mem_graphValueCandidateCodes upperAct upper (a.principalFix E) z.val psi).1 member).2,
      M.graphValueCandidateCodes_hs upperAct upper (a.principalSupportFamily ⊥ directed)
        (a.principalFix E) z.val symmetric psi member⟩
  · intro beta hBeta H ordinary nonempty
    have orderQ : upper.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq c.conditionOrder_code lifted stages packed]
      exact M.refinementHistoryOrder_mem pairing unions powers separation
        carrier forcingOrder hLifted hs hPacked omega
    let betaName : (M.nameDomain upper).names := ⟨Name.check upper ⊤ beta,
      M.check_mem upper ⊤ pairing unions powers separation collection
        (M.transitive hQ (upper.encode_mem ⊤)) beta hBeta⟩
    have checked : Name.eval {p | H.mem p} betaName.val = beta :=
      Name.eval_check {p | H.mem p} ⊤ H.top_mem beta
    obtain ⟨A, edge, x, hx⟩ := nonempty
    obtain ⟨sigma, child, same⟩ := Name.value_member_fourthDescendant upper {p | H.mem p}
      z.val beta A x edge hx
    have descendants := M.descendantFamilyCodes_mem upper pairing unions powers separation hQ
      z.val z.property 4
    let original : (M.nameDomain upper).names := ⟨sigma, M.transitive descendants child⟩
    have truth : Realize ((M.nameDomain upper).values {p | H.mem p})
        (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
        (evalAssignment {p | H.mem p} (extend original (extend z (extend betaName Fin.elim0)))) := by
      apply (realize_graphValueMember_values (M.nameDomain upper) {p | H.mem p} 0 1 2 _).2
      refine ⟨A, ?_, same.symm ▸ hx⟩
      change ZFSet.pair (Name.eval {p | H.mem p} betaName.val) A ∈ Name.eval {p | H.mem p} z.val
      rw [checked]
      exact edge
    obtain ⟨base, hBase, forced⟩ := (forcing_truth (M.nameDomain upper) H ordinary
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend original (extend z (extend betaName Fin.elim0)))).1 truth
    have existence : Forces (M.nameDomain upper)
        (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
        (extend z (extend betaName Fin.elim0)) base := by
      apply (forces_ex_iff (M.nameDomain upper) _ _ base).2
      intro q below
      exact ⟨q, le_rfl, original, forces_mono (M.nameDomain upper) _ _ forced below⟩
    have fixedBeta : a.principalFix V ≤ upperAct.stabilizer upper betaName.val :=
      fun g _ => upperAct.act_check upper g beta
    have density := fulfilled.structural_graphValue_candidates_dense collection infinite choice
      labels small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      z betaName V E base strict symmetric fixedZ fixedBeta existence
    obtain ⟨candidate, member, q, hq, recorded⟩ := M.ordinary_generic_candidate_witness upper
      pairing unions powers separation hQ orderQ collection
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend z (extend betaName Fin.elim0)) W groundW validW H ordinary hBase density
    have actual := (realize_graphValueMember_values (M.nameDomain upper) {p | H.mem p} 0 1 2
      (extend candidate (extend z (extend betaName Fin.elim0)))).1
        (forces_sound (M.nameDomain upper) H ordinary _ _ hq recorded)
    obtain ⟨value, edgeValue, memberValue⟩ := actual
    change ZFSet.pair (Name.eval {p | H.mem p} betaName.val) value ∈
      Name.eval {p | H.mem p} z.val at edgeValue
    rw [checked] at edgeValue
    exact ⟨candidate.val, member, value, edgeValue, memberValue⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
