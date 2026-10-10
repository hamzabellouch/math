import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticPreparedProfileSelections
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStructuralSupportPreparation

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def insertionUsedNodes
    (rowNodes columns row I T A nodes anchors : ZFSet.{u}) : ZFSet.{u} :=
  rowUsedRows rowNodes columns (natSetCode 2) row ∪
    relationImage (assignmentIndices I T A) nodes anchors

theorem mem_insertionUsedNodes
    (rowNodes columns row I T A nodes anchors v : ZFSet.{u}) :
    v ∈ insertionUsedNodes rowNodes columns row I T A nodes anchors ↔
      v ∈ rowUsedRows rowNodes columns (natSetCode 2) row ∨
      (v ∈ nodes ∧ ∃ idx ∈ I, ∃ u ∈ T, ∃ w ∈ T,
        stageOneAssignment idx u w ∈ A ∧ ZFSet.pair idx v ∈ anchors) := by
  rw [insertionUsedNodes, ZFSet.mem_union, mem_relationImage]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hv, idx, hi, edge⟩
    obtain ⟨hi, u, hu, w, hw, stored⟩ := (mem_assignmentIndices I T A idx).1 hi
    exact ⟨hv, idx, hi, u, hu, w, hw, stored, edge⟩
  · rintro ⟨hv, idx, hi, u, hu, w, hw, stored, edge⟩
    exact ⟨hv, idx, (mem_assignmentIndices I T A idx).2 ⟨hi, u, hu, w, hw, stored⟩, edge⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem insertionUsedNodes_mem_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rowNodes columns row I T A nodes anchors : ZFSet.{u}}
    (hRowNodes : rowNodes ∈ M.sets) (hColumns : columns ∈ M.sets)
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hAnchors : anchors ∈ M.sets)
    (rowCondition : row ∈ M.smallPartialFunctions (ZFSet.prod rowNodes columns) (natSetCode 2) ZFSet.omega)
    (rowSubset : rowNodes ⊆ nodes) (anchorFunction : ZFSet.IsFunc I nodes anchors)
    (smallA : M.groundEmbeddable A ZFSet.omega) :
    insertionUsedNodes rowNodes columns row I T A nodes anchors ∈ M.sets ∧
      M.groundEmbeddable (insertionUsedNodes rowNodes columns row I T A nodes anchors) ZFSet.omega ∧
      insertionUsedNodes rowNodes columns row I T A nodes anchors ⊆ nodes := by
  obtain ⟨hRows, smallRows⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite choice hRowNodes hColumns (M.natSetCode_mem separation infinite 2) rowCondition
  have omega := M.omega_mem separation infinite
  have hIndices := M.assignmentIndices_mem pairing unions powers separation hI hT hA
  have smallIndices := M.assignmentIndices_small pairing unions powers separation choice hI hT hA omega smallA
  have hUsedAnchors := M.relationImage_mem separation hIndices hNodes hAnchors
  have smallAnchors := M.groundEmbeddable_function_image pairing unions powers separation choice
    hIndices hNodes omega hAnchors anchorFunction smallIndices
  refine ⟨M.binary_union_mem pairing unions hRows hUsedAnchors,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hRows hUsedAnchors smallRows smallAnchors, ?_⟩
  intro v member
  rcases ZFSet.mem_union.1 member with usedRow | usedAnchor
  · exact rowSubset (rowUsedRows_subset _ _ _ _ usedRow)
  · exact ((mem_relationImage _ _ _ _).1 usedAnchor).1

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_insertion_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (h : G) (D K V : L),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      a.iso h D ≤ K → h ∈ a.principalFix V →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) →
        i.val ≤ K → i.val ≤ V) →
      ∃ q : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega),
        SetMembers.raw q = SetMembers.raw p ∪ SetMembers.raw (act.iso h p) ∧
        q ≤ p ∧ q ≤ act.iso h p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p h D K V bound cap fixed avoid
  apply M.countableFunction_common_extension pairing unions powers separation infinite choice
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) p (act.iso h p)
  intro x y z left right
  have pc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega p).2.1
  have hc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega (act.iso h p)).2.1
  have coords := (ZFSet.pair_mem_prod.1 (pc.shape left)).1
  have hz := (ZFSet.pair_mem_prod.1 (hc.shape right)).2
  obtain ⟨row, hrow, col, hcol, rfl⟩ := ZFSet.mem_prod.1 coords
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier row).1 hrow
  have oldUsed := row_mem_rowUsedRows pc left
  have movedBound := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h p D bound i (row_mem_rowUsedRows hc right)
  have same := fixed i.val (avoid i oldUsed (le_trans movedBound cap))
  have old := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph h p i col z hcol hz).1 (by rw [same]; exact right)
  exact pc.unique _ y z left old

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
include fulfilled

theorem generated_insertion (infinite : Realize M.sets infinity Fin.elim0)
    {A c e d : ZFSet.{u}} (hA : A ∈ M.sets)
    (subset : A ⊆ (run.finalGeometry i₀).carrier) (nonempty : A.Nonempty)
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ a ∈ A, ZFSet.pair e a ∈ (run.finalGeometry i₀).order) :
    let geometry := run.finalGeometry i₀
    let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph A
    F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
      A ⊆ F ∧
      (∀ T, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph T → A ⊆ T → F ⊆ T) ∧
      (∀ x ∈ F, ZFSet.pair e x ∈ geometry.order) ∧
      ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
        FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
          geometry.meetGraph geometry.action c e d F caps actors := by
  let geometry := run.finalGeometry i₀
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph A
  have ground : F ∈ M.sets := M.generatedMeetFilter_mem pairing unions powers separation infinite
    geometry.carrier_ground geometry.order_ground geometry.meet_ground hA
  have filter := M.generatedMeetFilter_filter pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset nonempty
  have contains := M.generatedMeetFilter_contains pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset
  have allAbove := M.generatedMeetFilter_lower_bound pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset he above
  exact ⟨ground, filter, contains,
    fun _ code includes => M.generatedMeetFilter_least pairing unions separation infinite
      geometry.carrier_ground geometry.meet subset code includes,
    allAbove, fulfilled.insertion c hc e he d hd F ground filter lower strict bound allAbove⟩

theorem decoded_generated_insertion (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (subset : A ⊆ (run.finalGeometry i₀).carrier) (nonempty : A.Nonempty)
    (c e d : SetMembers (run.finalGeometry i₀).carrier)
    (lower : ZFSet.pair (SetMembers.raw c) (SetMembers.raw e) ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair (SetMembers.raw e) (SetMembers.raw c) ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair (SetMembers.raw c) (SetMembers.raw d) ∈ (run.finalGeometry i₀).order)
    (above : ∀ a ∈ A, ZFSet.pair (SetMembers.raw e) a ∈ (run.finalGeometry i₀).order) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph A
    Compression.RecursiveMaps.HasInsertionFamily
      (geometry.action_code.toOrderAction geometry.group_code geometry.meet)
      (SetMembers Labels) c e d (fun x => SetMembers.raw x ∈ F) := by
  obtain ⟨_, filter, _, _, _, caps, _, actors, _, family⟩ :=
    fulfilled.generated_insertion infinite hA subset nonempty
      (SetMembers.raw_mem c) (SetMembers.raw_mem e) (SetMembers.raw_mem d) lower strict bound above
  exact family.hasInsertionFamily (run.finalGeometry i₀).group_code
    (run.finalGeometry i₀).meet (run.finalGeometry i₀).action_code filter

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
include fulfilled

theorem generated_insertion_exceptions
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (hLabels : Labels ∈ M.sets)
    {generators c e d Used Profiles extra : ZFSet.{u}}
    (hGenerators : generators ∈ M.sets)
    (subset : generators ⊆ (run.finalGeometry i₀).carrier) (nonempty : generators.Nonempty)
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ a ∈ generators, ZFSet.pair e a ∈ (run.finalGeometry i₀).order)
    (hUsed : Used ∈ M.sets) (hProfiles : Profiles ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : Used ⊆ (run.finalGeometry i₀).carrier)
    (filters : ∀ profile ∈ Profiles, MeetFilterCode (run.finalGeometry i₀).carrier
      (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph profile)
    (smallUsed : M.groundEmbeddable Used ZFSet.omega)
    (smallProfiles : M.groundEmbeddable Profiles ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) (extraSubset : extra ⊆ Labels) :
    let geometry := run.finalGeometry i₀
    let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
    F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
      generators ⊆ F ∧
      (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
        generators ⊆ filter → F ⊆ filter) ∧
      (∀ x ∈ F, ZFSet.pair e x ∈ geometry.order) ∧
      ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
        FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
          geometry.meetGraph geometry.action c e d F caps actors ∧
        ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
          ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
            (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order →
              ZFSet.pair node c ∈ geometry.order) ∧
            (∀ profile ∈ Profiles, c ∉ profile → cap ∉ profile) := by
  let geometry := run.finalGeometry i₀
  obtain ⟨groundF, filter, contains, least, allAbove, caps, hCaps, actors, hActors, family⟩ :=
    fulfilled.generated_insertion infinite hGenerators subset nonempty hc he hd lower strict bound above
  exact ⟨groundF, filter, contains, least, allAbove, caps, hCaps, actors, hActors, family,
    family.exists_ground_countable_exceptions M pairing unions powers separation infinite choice
      hLabels geometry.carrier_ground geometry.order_ground (M.transitive geometry.carrier_ground hc)
      hCaps hUsed hProfiles hExtra geometry.meet usedSubset filters smallUsed smallProfiles
      smallExtra extraSubset⟩

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

theorem structural_insertion_exceptions
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (_hmu : mu ∈ M.sets) (_muOrdinal : ordinalSetProperty mu) :
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
  ∀ (generators c0 e0 d0 extra : ZFSet.{u}), Labels ∈ M.sets →
    generators ∈ M.sets → generators ⊆ geometry.carrier → generators.Nonempty →
    c0 ∈ geometry.carrier → e0 ∈ geometry.carrier → d0 ∈ geometry.carrier →
    ZFSet.pair c0 e0 ∈ geometry.order → ZFSet.pair e0 c0 ∉ geometry.order →
    ZFSet.pair c0 d0 ∈ geometry.order →
    (∀ generator ∈ generators, ZFSet.pair e0 generator ∈ geometry.order) →
    extra ∈ M.sets → M.groundEmbeddable extra ZFSet.omega → extra ⊆ Labels →
  let L := ZFSet.prod stages (M.preparationWitnessBound s.carrier lifted upperQ)
  let Used := insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
    indices lifted A s.carrier anchors
  ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
    selections ⊆ M.preparedWitnessSelections c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode row) A) A ∧
    relationImage A L selections ∈ M.sets ∧
    M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  Used ∈ M.sets ∧ M.groundEmbeddable Used ZFSet.omega ∧ Used ⊆ geometry.carrier ∧
  Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
    (∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
    (∀ x alpha sourceRow sourceA k enumerations z F B f,
      ZFSet.pair x (ZFSet.pair alpha
        (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles) ∧
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair e0 x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action c0 e0 d0 F caps actors ∧
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
    ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order → ZFSet.pair node c0 ∈ geometry.order) ∧
      (∀ profile ∈ Profiles, c0 ∉ profile → cap ∉ profile) := by
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared generators c0 e0 d0 extra hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above hExtra smallExtra extraSubset
  have profileSelection := M.semanticStructuralTrace_preparedProfileSelection c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace infinite choice
    condition prepared
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    profilesGround, profilesSmall, profileFilters, coverage⟩ := profileSelection
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  have meetEq : canonicalMeetGraph s.carrier s.conditionOrder = geometry.meetGraph := by
    rw [geometry.decoded_order_eq]
    exact geometry.meet.eq_canonicalMeetGraph.symm
  have filters : ∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F := by
    intro F member
    have filter := profileFilters F member
    rw [meetEq, geometry.decoded_order_eq] at filter
    exact filter
  have candidate := ((M.mem_refinementHistoryForcing c.carrier lifted stages packed _).1 condition).1
  have Adata := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  obtain ⟨indicesGround, anchorsGround, anchorFunction⟩ := M.structuralIndexAnchorData
    b.carrier s.carrier s.conditionOrder (supportBasisCode s b a.principalFix) lifted squared
    stages history pairing unions powers separation collection hG hL order supports hLifted hSquared hs hh
  have used := M.insertionUsedNodes_mem_small pairing unions powers separation infinite choice
    (M.nonbottom_carrier_mem s separation hL) hColumns indicesGround hLifted Adata.2.1 hL
    anchorsGround (SetMembers.raw_mem row) (fun _ h => (s.mem_nonbottom_carrier _).1 h |>.1)
    anchorFunction Adata.2.2.2
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    used.1, used.2.1, used.2.2, profilesGround, profilesSmall, filters, coverage, ?_⟩
  exact fulfilled.generated_insertion_exceptions infinite choice hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above used.1 profilesGround hExtra used.2.2
    filters used.2.1 profilesSmall smallExtra extraSubset






theorem structural_compatible_insertion_unions
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
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
  ∀ (generators c0 e0 d0 extra : ZFSet.{u}), Labels ∈ M.sets →
    generators ∈ M.sets → generators ⊆ geometry.carrier → generators.Nonempty →
    c0 ∈ geometry.carrier → e0 ∈ geometry.carrier → d0 ∈ geometry.carrier →
    ZFSet.pair c0 e0 ∈ geometry.order → ZFSet.pair e0 c0 ∉ geometry.order →
    ZFSet.pair c0 d0 ∈ geometry.order →
    (∀ generator ∈ generators, ZFSet.pair e0 generator ∈ geometry.order) →
    extra ∈ M.sets → M.groundEmbeddable extra ZFSet.omega → extra ⊆ Labels →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) d0 ∈ geometry.order) →
    (∀ z ∈ A, ZFSet.pair z d0 ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  let L := ZFSet.prod stages (M.preparationWitnessBound s.carrier lifted upperQ)
  let Used := insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
    indices lifted A s.carrier anchors
  ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
    selections ⊆ M.preparedWitnessSelections c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode row) A) A ∧
    relationImage A L selections ∈ M.sets ∧
    M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  Used ∈ M.sets ∧ M.groundEmbeddable Used ZFSet.omega ∧ Used ⊆ geometry.carrier ∧
  Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
    (∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
    (∀ x alpha sourceRow sourceA k enumerations z F B f,
      ZFSet.pair x (ZFSet.pair alpha
        (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles) ∧
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair e0 x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    ∃ family : FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action c0 e0 d0 F caps actors,
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
    (∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order → ZFSet.pair node c0 ∈ geometry.order) ∧
      (∀ profile ∈ Profiles, c0 ∉ profile → cap ∉ profile)) ∧
    (¬ M.groundEmbeddable Labels ZFSet.omega → ∃ label ∈ Labels, label ∉ bad) ∧
    ∀ label : SetMembers Labels, SetMembers.raw label ∉ bad →
      let h := family.decodedActors label
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared generators c0 e0 d0 extra hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above hExtra smallExtra extraSubset rowD dataD
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good⟩ :=
    fulfilled.structural_insertion_exceptions collection infinite choice columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared generators c0 e0 d0 extra
      hLabels hGenerators generatorSubset generatorNonempty hc he hd lower strict bound above
      hExtra smallExtra extraSubset
  have available : ¬ M.groundEmbeddable Labels ZFSet.omega → ∃ label ∈ Labels, label ∉ bad := by
    classical
    intro notSmall
    by_contra none
    apply notSmall
    have equal : bad = Labels := by
      apply ZFSet.ext
      intro label
      exact ⟨fun member => badSubset member, fun member => by
        by_contra outside
        exact none ⟨label, member, outside⟩⟩
    rwa [equal] at badSmall
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good, available, ?_⟩
  intro label goodLabel
  let h := family.decodedActors label
  let cap := family.decodedCaps label
  let V : SetMembers geometry.carrier := SetMembers.ofMem c0 hc
  let D0 : SetMembers geometry.carrier := SetMembers.ofMem d0 hd
  have actorEdge := family.decodedActors_entry label
  have capEdge := family.decodedCaps_entry label
  have goodLaws := good _ _ capEdge goodLabel
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    apply (geometry.action_code.act_eq_iff h v v).2
    apply family.fixes _ _ actorEdge _ (SetMembers.raw_mem v)
    change ZFSet.pair (SetMembers.raw v) (SetMembers.raw V) ∈ geometry.order at hv
    simpa only [V, SetMembers.raw_ofMem] using hv
  have belowCap : a.iso h D0 ≤ cap := by
    change ZFSet.pair (SetMembers.raw (a.iso h D0)) (SetMembers.raw cap) ∈ geometry.order
    apply family.dominates _ _ _ actorEdge capEdge _ (SetMembers.raw_mem _)
    have entry : ZFSet.pair (ZFSet.pair (SetMembers.raw h) (SetMembers.raw D0))
        (SetMembers.raw (a.iso h D0)) ∈ geometry.action := geometry.action_code.act_mem h D0
    change ZFSet.pair (ZFSet.pair (SetMembers.raw h) d0)
      (SetMembers.raw (a.iso h D0)) ∈ geometry.action
    simpa only [D0, SetMembers.raw_ofMem] using entry
  have usedD (i : {i : SetMembers geometry.carrier // i ≠ ⊥})
      (used : s.encode i.val ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row)) :
      i.val ≤ D0 := by
    change ZFSet.pair (SetMembers.raw i.val) (SetMembers.raw D0) ∈ geometry.order
    have bound : ZFSet.pair (SetMembers.raw i.val) d0 ∈ geometry.order := rowD i.val used
    simpa only [D0, SetMembers.raw_ofMem] using bound
  have avoidRows (i : {i : SetMembers geometry.carrier // i ≠ ⊥})
      (used : s.encode i.val ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row))
      (below : i.val ≤ cap) : i.val ≤ V := by
    change ZFSet.pair (SetMembers.raw i.val) (SetMembers.raw V) ∈ geometry.order
    rw [SetMembers.raw_ofMem]
    exact goodLaws.1 _ (ZFSet.mem_union.2 (Or.inl used)) below
  obtain ⟨commonRow, rowCode, below, belowH⟩ := M.internalRowAction_insertion_union a s b columns
    pairing unions powers separation infinite hL hC hG graph choice row h D0 cap V usedD belowCap fixed avoidRows
  have candidate := ((M.mem_refinementHistoryForcing c.carrier lifted stages packed _).1 condition).1
  have Adata := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have originalData : ∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈
      stageOneDataBounds A indices lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples := by
    have code : s.encode D0 = d0 := SetMembers.raw_ofMem d0 hd
    rw [code]
    exact dataD
  have transported := M.binaryRowStructuralAssignmentImage_dataBound a s b columns pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h D0 A Adata.2.1 originalData
  have anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A → ZFSet.pair idx E ∈ anchors →
      ZFSet.pair E (s.encode cap) ∈ s.conditionOrder → ZFSet.pair E (s.encode V) ∈ s.conditionOrder := by
    intro idx u w E assignment anchor lowerCap
    have fields := (stageOneAssignment_mem_assignments indices lifted idx u w).1 (Adata.2.2.1 assignment)
    have Ebound : E ∈ s.carrier := (ZFSet.pair_mem_prod.1
      ((M.structuralIndexAnchors_function b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared stages history).1 anchor)).2
    have used := (mem_insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
      indices lifted A s.carrier anchors E).2 (Or.inr
        ⟨Ebound, idx, fields.1, u, fields.2.1, w, fields.2.2, assignment, anchor⟩)
    rw [geometry.decoded_order_eq] at lowerCap ⊢
    change ZFSet.pair E (SetMembers.raw V) ∈ geometry.order
    rw [SetMembers.raw_ofMem]
    exact goodLaws.1 E used lowerCap
  have profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections,
      s.encode V ∉ F → s.encode cap ∉ F := by
    have code : s.encode V = c0 := SetMembers.raw_ofMem c0 hc
    rw [code]
    exact goodLaws.2
  have unionFacts := M.semanticStructuralTrace_insertion_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small indices S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b columns pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    row commonRow A selections h D0 cap V condition function selected rangeGround rangeSmall
    below belowH fixed belowCap anchorGood profileGood transported.2.2
  exact ⟨commonRow, rowCode, unionFacts⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [PartialOrder L]

theorem compressed_name_support (a : PosetAction G P) (s : Presentation P)
    (d : PosetAction G L) (g : G) (D E : L) (tau : Name s)
    (support : d.principalFix D ≤ a.stabilizer s tau)
    (below : d.iso g D ≤ E) :
    d.principalFix E ≤ a.stabilizer s (a.act s g tau) := by
  rw [a.stabilizer_conjugation]
  have moved : d.principalFix (d.iso g D) ≤
      (a.stabilizer s tau).map (Compression.RecursiveMaps.CosetGeometry.OrderAction.conjugateHom g) := by
    rw [← principalFix_map_conjugate]
    exact Subgroup.map_mono support
  exact le_trans (d.principalFix_antitone below) moved

end PartitionPilot.Forcing.PosetAction

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

theorem structural_compression
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
  ∀ (V E D0 : SetMembers geometry.carrier), V < E → V ≤ D0 →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
    (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  ∃ (h : SetMembers geometry.actors) (cap : SetMembers geometry.carrier),
    h ∈ a.principalFix V ∧ V < cap ∧ cap ≤ E ∧ a.iso h D0 ≤ cap ∧
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared V E D0 lower bound rowD dataD
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have labelGround : Labels ∈ M.sets := labels.symm ▸ spec.1
  have labelLarge : ¬ M.groundEmbeddable Labels ZFSet.omega := labels.symm ▸ spec.2.2.2
  have generatorGround : ({s.encode E} : ZFSet.{u}) ∈ M.sets :=
    M.insert_mem pairing unions (M.transitive hL (s.encode_mem E)) (M.empty_mem ⟨s.carrier, hL⟩)
  have generatorSubset : ({s.encode E} : ZFSet.{u}) ⊆ geometry.carrier := by
    intro z hz
    have same := ZFSet.mem_singleton.1 hz
    subst z
    exact s.encode_mem E
  have generatorNonempty : ({s.encode E} : ZFSet.{u}).Nonempty :=
    ⟨s.encode E, ZFSet.mem_singleton.2 rfl⟩
  have above : ∀ z ∈ ({s.encode E} : ZFSet.{u}), ZFSet.pair (s.encode E) z ∈ geometry.order := by
    intro z hz
    have same := ZFSet.mem_singleton.1 hz
    subst z
    exact geometry.meet.order.refl _ (s.encode_mem E)
  have rawRowD : ∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) (s.encode D0) ∈ geometry.order := fun i hi => rowD i hi
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good, available, unionsFor⟩ :=
    fulfilled.structural_compatible_insertion_unions collection infinite choice small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared
      {s.encode E} (s.encode V) (s.encode E) (s.encode D0) ∅
      labelGround generatorGround generatorSubset generatorNonempty (s.encode_mem V)
      (s.encode_mem E) (s.encode_mem D0) (le_of_lt lower) (not_le_of_gt lower) bound above
      (M.empty_mem ⟨s.carrier, hL⟩) (M.empty_groundEmbeddable ZFSet.omega ⟨s.carrier, hL⟩)
      (fun _ member => (ZFSet.notMem_empty _ member).elim) rawRowD dataD
  obtain ⟨label, labelMember, goodLabel⟩ := available labelLarge
  let chosen : SetMembers Labels := SetMembers.ofMem label labelMember
  have chosenGood : SetMembers.raw chosen ∉ bad := by
    simpa only [chosen, SetMembers.raw_ofMem] using goodLabel
  let h := family.decodedActors chosen
  let cap := family.decodedCaps chosen
  have actorEdge := family.decodedActors_entry chosen
  have capEdge := family.decodedCaps_entry chosen
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    exact (geometry.action_code.act_eq_iff h v v).2
      (family.fixes _ _ actorEdge _ (s.encode_mem v) hv)
  have profile := family.profiles _ _ capEdge
  have strictCap : V < cap := lt_iff_le_not_ge.2 ⟨profile.target_below_cap, profile.cap_not_below_target⟩
  have capBelow : cap ≤ E :=
    ((family.tests geometry.meet.order filterCode capEdge (s.encode_mem E)
      (geometry.meet.order.refl _ (s.encode_mem E))).1
        (contains (ZFSet.mem_singleton.2 rfl)))
  have movedBound : a.iso h D0 ≤ cap :=
    family.dominates _ _ _ actorEdge capEdge _ (s.encode_mem _) (geometry.action_code.act_mem h D0)
  exact ⟨h, cap, fixed, strictCap, capBelow, movedBound, unionsFor chosen chosenGood⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
