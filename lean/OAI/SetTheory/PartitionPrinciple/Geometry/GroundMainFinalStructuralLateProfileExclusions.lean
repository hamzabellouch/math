import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStructuralCompression

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

theorem structural_compatible_insertion_with_late_profiles
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable)
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
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  ∀ (row : SetMembers c.carrier) (A : ZFSet.{u}),
    ZFSet.pair (c.encode row) A ∈ upperQ →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (ZFSet.pair (c.encode row) A) →
  ∀ (V E D0 : SetMembers geometry.carrier) (generators lateProfiles : ZFSet.{u}),
    V < E → V ≤ D0 → generators ∈ M.sets → generators ⊆ geometry.carrier →
    generators.Nonempty → (∀ z ∈ generators, ZFSet.pair (s.encode E) z ∈ geometry.order) →
    lateProfiles ∈ M.sets → M.groundEmbeddable lateProfiles ZFSet.omega →
    (∀ profile ∈ lateProfiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph profile) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
    (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair (s.encode E) x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    ∃ family : FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action (s.encode V) (s.encode E) (s.encode D0) F caps actors,
  ∃ badComp ∈ M.sets, badComp ⊆ Labels ∧ M.groundEmbeddable badComp ZFSet.omega ∧
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ badComp ⊆ bad ∧
    (∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      ∀ profile ∈ lateProfiles, s.encode V ∉ profile → cap ∉ profile) ∧
    (∃ label : SetMembers Labels, SetMembers.raw label ∉ bad) ∧
    ∀ label : SetMembers Labels, SetMembers.raw label ∉ bad →
      let h := family.decodedActors label
      let cap := family.decodedCaps label
      h ∈ a.principalFix V ∧ V < cap ∧ ¬ E ≤ cap ∧ a.iso h D0 ≤ cap ∧
      (∀ v : SetMembers geometry.carrier, E ≤ v →
        (s.encode v ∈ F → cap ≤ v) ∧
        (s.encode v ∉ F → ZFSet.pair (ZFSet.pair (s.encode cap) (s.encode v))
          (s.encode V) ∈ geometry.meetGraph)) ∧
      let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
      ∃ commonRow : SetMembers c.carrier,
        SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso h row) ∧
        ZFSet.pair (c.encode commonRow) (A ∪ movedA) ∈ upperQ ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) (ZFSet.pair (c.encode row) A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA))
          (ZFSet.pair (c.encode (act.iso h row)) movedA) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed := by
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
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared V E D0 generators lateProfiles lower bound
    hGenerators generatorSubset generatorNonempty above hProfiles smallProfiles profileFilters rowD dataD
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have labelGround : Labels ∈ M.sets := labels.symm ▸ spec.1
  have labelLarge : ¬ M.groundEmbeddable Labels ZFSet.omega := labels.symm ▸ spec.2.2.2
  have emptyGround := M.empty_mem ⟨s.carrier, hL⟩
  have emptySmall := M.empty_groundEmbeddable ZFSet.omega ⟨s.carrier, hL⟩
  have rawRowD : ∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) (s.encode D0) ∈ geometry.order := fun i hi => rowD i hi
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, preparedProfileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, containsExtra, good, available, unionsFor⟩ :=
    fulfilled.structural_compatible_insertion_unions collection infinite choice small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared
      generators (s.encode V) (s.encode E) (s.encode D0) ∅
      labelGround hGenerators generatorSubset generatorNonempty (s.encode_mem V)
      (s.encode_mem E) (s.encode_mem D0) (le_of_lt lower) (not_le_of_gt lower) bound above
      emptyGround emptySmall (fun _ member => (ZFSet.notMem_empty _ member).elim) rawRowD dataD
  obtain ⟨bad, hBad, badSubset, badSmall, containsComp, lateGood⟩ :=
    family.exists_ground_countable_exceptions M pairing unions powers separation infinite choice
      labelGround hL geometry.order_ground (M.transitive hL (s.encode_mem V)) hCaps
      emptyGround hProfiles hBadComp geometry.meet
      (fun _ member => (ZFSet.notMem_empty _ member).elim)
      profileFilters emptySmall smallProfiles badCompSmall badCompSubset
  have survivor : ∃ label : SetMembers Labels, SetMembers.raw label ∉ bad := by
    classical
    by_contra none
    apply labelLarge
    have equal : bad = Labels := by
      apply ZFSet.ext
      intro label
      refine ⟨fun member => badSubset member, ?_⟩
      intro member
      by_contra outside
      exact none ⟨SetMembers.ofMem label member, by simpa only [SetMembers.raw_ofMem] using outside⟩
    rwa [equal] at badSmall
  refine ⟨filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, bad, hBad, badSubset, badSmall,
    containsComp, fun label cap entry outside => (lateGood label cap entry outside).2, survivor, ?_⟩
  intro label outside
  have compGood : SetMembers.raw label ∉ badComp := fun member => outside (containsComp member)
  let h := family.decodedActors label
  let cap := family.decodedCaps label
  have actorEdge := family.decodedActors_entry label
  have capEdge := family.decodedCaps_entry label
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    exact (geometry.action_code.act_eq_iff h v v).2
      (family.fixes _ _ actorEdge _ (s.encode_mem v) hv)
  have profile := family.profiles _ _ capEdge
  have strictCap : V < cap := lt_iff_le_not_ge.2 ⟨profile.target_below_cap, profile.cap_not_below_target⟩
  have movedBound : a.iso h D0 ≤ cap :=
    family.dominates _ _ _ actorEdge capEdge _ (s.encode_mem _) (geometry.action_code.act_mem h D0)
  exact ⟨fixed, strictCap, profile.separator_not_below_cap, movedBound,
    fun v aboveV => family.tests geometry.meet.order filterCode capEdge (s.encode_mem v) aboveV,
    unionsFor label compGood⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
