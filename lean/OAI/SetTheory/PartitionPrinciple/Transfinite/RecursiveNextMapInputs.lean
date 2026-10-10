import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchEmbeddingRecognition
import OAI.SetTheory.PartitionPrinciple.Geometry.LiftedCompressionEmbeddings

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundRecursiveAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L rD rL μD μL Qs rs μs As Es Fs Ss Maps Sources : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (target : MeetOrderCode L rL μL) (maps : FunctionGraphOn I Maps)
    (sources : ZFSet.IsFunc I D Sources)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → MeetEmbeddingCode D L rD rL μD μL S)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) :
    let K := recursiveAttachmentIndices I J D (⋃₀ ⋃₀ Fs) Sources Fs
    K ∈ M.sets ∧
    (∀ i j a F, ZFSet.pair i a ∈ Sources → ZFSet.pair j F ∈ Fs →
      (ZFSet.pair i j ∈ K ↔ a ∉ F)) ∧
    ∃ next : AttachmentBatchInputs L rL μL K
      (pairSecondField I J K Qs) (pairSecondField I J K rs)
      (pairSecondField I J K μs) (pairSecondField I J K As)
      (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps)
      (M.groundPairPushFilters K I J L rL Maps Fs)
      (recursiveSeparatorFamily K I J D L Maps Ss),
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      ∃ family ∈ M.sets, FunctionGraphOn K family ∧
        (∀ i f, ZFSet.pair i f ∈ family ↔ i ∈ K ∧
          f = batchTemplateGraph K L (pairSecondField I J K Qs)
            (pairSecondField I J K rs) (pairSecondField I J K As)
            (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps) i) ∧
        ∀ (i : {i : ZFSet.{u} // i ∈ K}) f, ZFSet.pair i.val f ∈ family →
          MeetEmbeddingCode (next.space i) next.batchCarrier (next.rel i) next.batchOrder
            (next.meet i) next.batchMeetGraph f := by
  dsimp only
  let K := recursiveAttachmentIndices I J D (⋃₀ ⋃₀ Fs) Sources Fs
  have hK : K ∈ M.sets := M.recursiveAttachmentIndices_mem pairing unions powers separation
    hI hJ hD (M.union_mem unions (M.union_mem unions hFs)) hSources hFs
  have subset : K ⊆ ZFSet.prod I J := recursiveAttachmentIndices_subset _ _ _ _ _ _
  have fields {H : ZFSet.{u}} (hH : H ∈ M.sets) : pairSecondField I J K H ∈ M.sets :=
    M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK
      (M.union_mem unions (M.union_mem unions hH)) hH
  have composites := M.groundPairCompositions_spec pairing unions powers separation hK hI hJ
    (M.familyPointBound_mem unions hQs) hD hL hEs hMaps d.embeddings maps subset
  have filters := M.groundPairPushFilters_spec pairing unions powers separation
    hK hI hJ hL hrL hMaps hFs maps d.filters subset
  let next := M.groundRecursiveBatchInputs pairing unions powers separation d target maps valid subset
    hK hI hJ hD hL hrL hQs hEs hFs hMaps
  refine ⟨hK, ?_, next, ?_⟩
  · intro i j a F source filter
    exact recursiveAttachmentIndices_entry_iff sources d.filters.to_isFunc source filter
  · exact M.exists_batchAttachment_embedding_family pairing unions powers separation next
      hL hrL hK (fields hQs) (fields hrs) (fields hμs) (fields hAs)
      composites.1 filters.1
      (M.recursiveSeparatorFamily_mem pairing unions powers separation hK hI hJ hD hL hMaps hSs)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

noncomputable abbrev groundLiftFamily (next : h.NextInputs M) :=
  M.groundLiftedCompressionFamily I J D d.batchCarrier next.batchCarrier
    (indexedAttachmentFresh J Qs rs As) (familyPointBound Qs) Maps Sources Fs Reps G A

theorem groundLiftFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (next : h.NextInputs M) (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : d.batchCarrier ∈ M.sets) (hC : next.batchCarrier ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    h.liftGraph M next ∈ M.sets ∧ h.groundLiftFamily M next ∈ M.sets ∧
      FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        ZFSet.IsFunc d.batchCarrier next.batchCarrier f := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hJ hQs hrs hAs
  have hB := M.familyPointBound_mem unions hQs
  have graph := M.liftedCompressionGraph_mem pairing unions powers separation
    hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  obtain ⟨member, function, entries⟩ := M.groundLiftedCompressionFamily_spec
    pairing unions powers separation hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  refine ⟨graph, member, function, entries, ?_⟩
  intro i f entry
  obtain ⟨hi, rfl⟩ := (entries i f).1 entry
  exact h.liftSection_function M next hi

theorem exists_groundLiftGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧ FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        ZFSet.IsFunc d.batchCarrier next.batchCarrier f := by
  obtain ⟨hL, hrL, _, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hD hrD hJ hQs hrs hμs hAs hEs hFs
  obtain ⟨_, _, next, hC, hrC, hμC, meet, _⟩ := M.groundRecursiveAttachment
    pairing unions powers separation d d.batch_meetOrder h.maps h.sources h.valid
    hI hJ hD hL hrL hQs hrs hμs hAs hEs hFs hSs hMaps hSources
  obtain ⟨graph, family, function, entries, functions⟩ := h.groundLiftFamily_spec M
    pairing unions powers separation next hI hJ hD hL hC hQs hrs hAs
    hMaps hSources hFs hReps hG hA
  exact ⟨next, hC, hrC, hμC, meet, graph, h.liftGraph_function M next,
    family, function, entries, functions⟩

end PartitionPilot.Forcing.CodedRecursiveMapInputs

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleRecursiveAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Qs := constantFamilyGraph I P
    let rs := constantFamilyGraph I r
    let μs := constantFamilyGraph I μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Fs := literalTaskFilterGraph I P R U Labels
    let Ss := literalTaskSeparatorGraph I P R U Labels
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let Maps := M.batchEmbeddingFamily I P Qs rs As Es
    let K := recursiveAttachmentIndices I I P (⋃₀ ⋃₀ Fs) As Fs
    K ∈ M.sets ∧
    (∀ i j a F, ZFSet.pair i a ∈ As → ZFSet.pair j F ∈ Fs →
      (ZFSet.pair i j ∈ K ↔ a ∉ F)) ∧
    ∃ next : AttachmentBatchInputs d.batchCarrier d.batchOrder d.batchMeetGraph K
      (pairSecondField I I K Qs) (pairSecondField I I K rs)
      (pairSecondField I I K μs) (pairSecondField I I K As)
      (M.groundPairCompositions K I I (familyPointBound Qs) P d.batchCarrier Es Maps)
      (M.groundPairPushFilters K I I d.batchCarrier d.batchOrder Maps Fs)
      (recursiveSeparatorFamily K I I P d.batchCarrier Maps Ss),
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      ∃ family ∈ M.sets, FunctionGraphOn K family ∧
        (∀ i f, ZFSet.pair i f ∈ family ↔ i ∈ K ∧
          f = batchTemplateGraph K d.batchCarrier (pairSecondField I I K Qs)
            (pairSecondField I I K rs) (pairSecondField I I K As)
            (M.groundPairCompositions K I I (familyPointBound Qs) P d.batchCarrier Es Maps) i) ∧
        ∀ (i : {i : ZFSet.{u} // i ∈ K}) f, ZFSet.pair i.val f ∈ family →
          MeetEmbeddingCode (next.space i) next.batchCarrier (next.rel i) next.batchOrder
            (next.meet i) next.batchMeetGraph f := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Qs := constantFamilyGraph I P
  let rs := constantFamilyGraph I r
  let As := literalTaskSourceGraph I P R U Labels
  let Es := literalTaskBaseGraph I P R U Labels
  let Maps := M.batchEmbeddingFamily I P Qs rs As Es
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have initial := M.groundEligibleTaskAttachment pairing unions powers separation
    hP hG hr hμ hA hLabels group action meet
  obtain ⟨hMaps, maps, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  have valid : ∀ i S, ZFSet.pair i S ∈ Maps →
      MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph S := by
    intro i S entry
    obtain ⟨hi, equal⟩ := (entries i S).1 entry
    let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have spaceEq : d.space index = P :=
      ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry index)).2
    have relEq : d.rel index = r :=
      ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry index)).2
    have meetEq : d.meet index = μ :=
      ((pair_mem_constantFamilyGraph I μ _ _).1 (d.meet_entry index)).2
    rw [equal]
    simpa only [spaceEq, relEq, meetEq] using d.batch_template_embedding_code index
  exact M.groundRecursiveAttachment pairing unions powers separation d d.batch_meetOrder maps
    (fields 0).2 valid hI hI hP initial.1 initial.2.1 hQs hrs hμs
    (fields 0).1 (fields 2).1 (fields 4).1 (fields 3).1 hMaps (fields 0).1

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

theorem exists_groundLiftEmbeddings
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧ FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        MeetEmbeddingCode d.batchCarrier next.batchCarrier d.batchOrder next.batchOrder
          d.batchMeetGraph next.batchMeetGraph f ∧
        ∀ a g x y, ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
          x ∈ d.batchCarrier → ZFSet.pair x a ∈ d.batchOrder →
            (ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A) := by
  obtain ⟨next, hC, hrC, hμC, meet, graph, func, family, famFunc, entries, _⟩ :=
    h.exists_groundLiftGraphs M pairing unions powers separation hI hJ hD hrD
      hQs hrs hμs hAs hEs hFs hSs hMaps hSources hReps hG hA
  refine ⟨next, hC, hrC, hμC, meet, graph, func, family, famFunc, entries, ?_⟩
  intro i f entry
  obtain ⟨hi, rfl⟩ := (entries i f).1 entry
  refine ⟨h.liftSection_embedding M next ⟨i, hi⟩, ?_⟩
  intro a g x y source representative hx below
  exact h.liftSection_agrees_on_base M next source representative hx below

end PartitionPilot.Forcing.CodedRecursiveMapInputs

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs
open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include h in
theorem sources_on_current : ZFSet.IsFunc I d.batchCarrier Sources := by
  refine ⟨?_, h.sources.2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (h.sources.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hi, old_mem_taggedExtension ha⟩

theorem nextMapInputs_of_family
    (family : FunctionGraphOn I (h.groundLiftFamily M next))
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (action : PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T)) :
    CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T) := by
  refine ⟨family, h.sources_on_current, h.representatives, h.group, action, ?_, ?_⟩
  · intro i f entry
    obtain ⟨hi, rfl⟩ := (entries i f).1 entry
    exact h.liftSection_embedding M next ⟨i, hi⟩
  · intro i a g f x y source representative entry hx lower
    obtain ⟨_, rfl⟩ := (entries i f).1 entry
    exact (h.liftSection_agrees_on_base M next source representative hx lower).trans
      (h.nextAction_old_iff hx).symm

theorem ground_nextMapInputs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : d.batchCarrier ∈ M.sets) (hC : next.batchCarrier ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (action : PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T)) :
    h.groundLiftFamily M next ∈ M.sets ∧
      CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
        G m inv one (h.nextActionGraph T) := by
  obtain ⟨_, ground, family, entries, _⟩ := h.groundLiftFamily_spec M
    pairing unions powers separation next hI hJ hD hL hC hQs hrs hAs
      hMaps hSources hFs hReps hG hA
  exact ⟨ground, h.nextMapInputs_of_family M next family entries action⟩

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
