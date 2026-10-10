import OAI.SetTheory.PartitionPrinciple.Definability.AttachmentOldCodeLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.FixedCompressionSeeds

namespace OAI


namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem liftSection_old_iff {i S x y : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair x y ∈ h.liftSection M next i ↔ ZFSet.pair x y ∈ S := by
  rw [liftSection, pair_mem_indexedRelationSection, h.liftGraph_old_iff M next mapEntry hx]
  constructor
  · exact fun entry => entry.2.2
  · intro entry
    exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension
      (ZFSet.pair_mem_prod.1 ((h.valid i S mapEntry).injection.function.1 entry)).2, entry⟩

theorem liftSection_image_base_iff {i a S b x y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (mapEntry : ZFSet.pair i S ∈ Maps)
    (base : ZFSet.pair a b ∈ S) (image : ZFSet.pair x y ∈ h.liftSection M next i) :
    ZFSet.pair y b ∈ next.batchOrder ↔ ZFSet.pair x a ∈ d.batchOrder := by
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  exact h.liftSection_order_iff M next ⟨i, h.maps.pair_source mapEntry⟩ image
    ((h.liftSection_old_iff M next mapEntry ha).2 base)

theorem liftSection_cut_iff {i a S b x y z w : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (mapEntry : ZFSet.pair i S ∈ Maps)
    (base : ZFSet.pair a b ∈ S) (image : ZFSet.pair x y ∈ h.liftSection M next i)
    (cut : ZFSet.pair (ZFSet.pair x a) z ∈ d.batchMeetGraph) :
    ZFSet.pair (ZFSet.pair y b) w ∈ next.batchMeetGraph ↔
      ZFSet.pair z w ∈ h.liftSection M next i := by
  have hi := h.maps.pair_source mapEntry
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have baseLift := (h.liftSection_old_iff M next mapEntry ha).2 base
  have hz := (ZFSet.pair_mem_prod.1 (d.batch_meetOrder.operation.1 cut)).2
  constructor
  · intro targetCut
    obtain ⟨value, entry, _⟩ := (h.liftSection_function M next hi).2 z hz
    have equal : w = value :=
      (show FunctionGraphOn (ZFSet.prod next.batchCarrier next.batchCarrier) next.batchMeetGraph from
        ⟨next.batchCarrier, next.batch_meetOrder.operation⟩).unique targetCut
          (h.liftSection_map_meet M next ⟨i, hi⟩ cut image baseLift entry)
    exact equal.symm ▸ entry
  · intro entry
    exact h.liftSection_map_meet M next ⟨i, hi⟩ cut image baseLift entry

theorem liftSection_range_below_cap {i S T K x y : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (hT : T ∈ D)
    (top : ∀ p ∈ D, ZFSet.pair p T ∈ rD) (cap : ZFSet.pair T K ∈ S)
    (image : ZFSet.pair x y ∈ h.liftSection M next i) :
    ZFSet.pair y K ∈ next.batchOrder := by
  have hi := h.maps.pair_source mapEntry
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next hi).1 image)).1
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  have lower : ZFSet.pair (d.coding.encode X) T ∈ d.batchOrder :=
    (d.coding.le_encode X (.inl ⟨T, hT⟩)).2
      (d.templates.greatest_preserved ⟨T, hT⟩ (fun p => top p.val p.property) X)
  exact (h.liftSection_order_iff M next ⟨i, hi⟩ image
    ((h.liftSection_old_iff M next mapEntry hT).2 cap)).2 lower

theorem liftSection_fresh_outside_base {i a S b y : ZFSet.{u}}
    (q : d.templates.Fresh)
    (source : ZFSet.pair i a ∈ Sources) (mapEntry : ZFSet.pair i S ∈ Maps)
    (base : ZFSet.pair a b ∈ S) (negative : a ∉ d.filter q.1)
    (image : ZFSet.pair (d.coding.encode (.inr q)) y ∈ h.liftSection M next i) :
    ZFSet.pair y b ∉ next.batchOrder := by
  intro lower
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  exact negative ((d.coding.le_encode (.inr q) (.inl ⟨a, ha⟩)).1
    ((h.liftSection_image_base_iff M next source mapEntry base image).1 lower))





theorem negative_cap_persists {K v b w : ZFSet.{u}}
    (hK : K ∈ d.batchCarrier) (hv : v ∈ d.batchCarrier) (hb : b ∈ d.batchCarrier)
    (negative : ∀ z, ZFSet.pair (ZFSet.pair K v) z ∈ d.batchMeetGraph →
      ZFSet.pair z b ∈ d.batchOrder)
    (entry : ZFSet.pair (ZFSet.pair K v) w ∈ next.batchMeetGraph) :
    ZFSet.pair w b ∈ next.batchOrder := by
  have oldMeet := (next.old_meet_iff hK hv).1 entry
  have hw := (ZFSet.pair_mem_prod.1 (d.batch_meetOrder.operation.1 oldMeet)).2
  exact (next.old_order_iff hw hb).2 (negative w oldMeet)

theorem liftSection_cap_and_source_unchanged {i S T a K b : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (source : ZFSet.pair i a ∈ Sources)
    (hT : T ∈ D) (cap : ZFSet.pair T K ∈ S) (base : ZFSet.pair a b ∈ S) :
    ZFSet.pair T K ∈ h.liftSection M next i ∧
      ZFSet.pair a b ∈ h.liftSection M next i :=
  ⟨(h.liftSection_old_iff M next mapEntry hT).2 cap,
    (h.liftSection_old_iff M next mapEntry
      (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2).2 base⟩

theorem liftSection_negative_exclusion {i a S b T K v y : ZFSet.{u}}
    (q : d.templates.Fresh)
    (source : ZFSet.pair i a ∈ Sources) (mapEntry : ZFSet.pair i S ∈ Maps)
    (base : ZFSet.pair a b ∈ S) (hT : T ∈ D)
    (top : ∀ p ∈ D, ZFSet.pair p T ∈ rD) (cap : ZFSet.pair T K ∈ S)
    (hv : v ∈ d.batchCarrier)
    (negativeCap : ∀ w, ZFSet.pair (ZFSet.pair K v) w ∈ d.batchMeetGraph →
      ZFSet.pair w b ∈ d.batchOrder)
    (negativeComponent : a ∉ d.filter q.1)
    (image : ZFSet.pair (d.coding.encode (.inr q)) y ∈ h.liftSection M next i) :
    ZFSet.pair y v ∉ next.batchOrder := by
  intro below
  have embedding := h.valid i S mapEntry
  have hK := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 cap)).2
  have hb := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 base)).2
  have hy := (ZFSet.pair_mem_prod.1
    ((h.liftSection_function M next (h.maps.pair_source mapEntry)).1 image)).2
  obtain ⟨w, entry, _⟩ := next.batch_meetOrder.operation.2 (ZFSet.pair K v)
    (ZFSet.pair_mem_prod.2 ⟨old_mem_taggedExtension hK, old_mem_taggedExtension hv⟩)
  have lower := next.batch_meetOrder.greatest K v w y hy entry
    (h.liftSection_range_below_cap M next mapEntry hT top cap image) below
  have bound := h.negative_cap_persists M next hK hv hb negativeCap entry
  have hw := (ZFSet.pair_mem_prod.1 (next.batch_meetOrder.operation.1 entry)).2
  exact h.liftSection_fresh_outside_base M next q source mapEntry base negativeComponent image
    (next.batch_meetOrder.order.trans y hy w hw b (old_mem_taggedExtension hb) lower bound)

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing

universe u

namespace AttachmentBatchInputs

variable {P0 r0 μ0 D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)

theorem original_carrier_subset (original : P0 ⊆ D) : P0 ⊆ d.batchCarrier :=
  fun _ hx => old_mem_taggedExtension (original hx)

theorem original_order_iff (original : P0 ⊆ D)
    (restriction : ∀ x ∈ P0, ∀ y ∈ P0, ZFSet.pair x y ∈ rD ↔ ZFSet.pair x y ∈ r0)
    {x y : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair x y ∈ d.batchOrder ↔ ZFSet.pair x y ∈ r0 :=
  (d.old_order_iff (original hx) (original hy)).trans (restriction x hx y hy)

theorem original_meet_iff (original : P0 ⊆ D)
    (restriction : ∀ x ∈ P0, ∀ y ∈ P0, ∀ z,
      ZFSet.pair (ZFSet.pair x y) z ∈ μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0)
    {x y z : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ μ0 :=
  (d.old_meet_iff (original hx) (original hy)).trans (restriction x hx y hy z)

end AttachmentBatchInputs

namespace CodedRecursiveMapInputs

variable {P0 A0 D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

theorem nextAction_original_iff (original : P0 ⊆ D)
    (restriction : ∀ g x, x ∈ P0 → ∀ y,
      ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0)
    {g x y : ZFSet.{u}} (hx : x ∈ P0) :
    ZFSet.pair (ZFSet.pair g x) y ∈ h.nextActionGraph T ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A0 :=
  (h.nextAction_old_iff (d.original_carrier_subset original hx)).trans (restriction g x hx y)

end CodedRecursiveMapInputs






structure RecursiveCompressionInvariant
    {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
    (seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)
    {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : Prop where
  originalSubset : P0 ⊆ D
  originalOrder : ∀ x ∈ P0, ∀ y ∈ P0, ZFSet.pair x y ∈ rD ↔ ZFSet.pair x y ∈ r0
  originalMeet : ∀ x ∈ P0, ∀ y ∈ P0, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0
  originalAction : ∀ g x, x ∈ P0 → ∀ y,
    ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0
  top : ∀ x ∈ D, ZFSet.pair x τ ∈ rD
  agreement : ∀ g ∈ G, ∀ k ∈ G, ∀ v ∈ P0,
    ActionAgreementBelow P0 r0 A0 g k v →
      ActionAgreementBelow d.batchCarrier d.batchOrder A g k v
  negative : ∀ i S a F cap base v w,
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ Sources → ZFSet.pair i F ∈ Filters →
    ZFSet.pair τ cap ∈ S → ZFSet.pair a base ∈ S → v ∈ P0 → v ∉ F →
    ZFSet.pair (ZFSet.pair cap v) w ∈ d.batchMeetGraph → ZFSet.pair w base ∈ d.batchOrder

namespace RecursiveCompressionInvariant

variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)

include state s in
theorem compatible : RecursiveRepresentativeCompatibility h T := by
  intro δ i j a g k x y z transport source firstRep secondRep hx below first second
  have hδ := (s.taskAction.entry_shape transport).1
  have hg := (ZFSet.pair_mem_prod.1 (h.representatives.1 firstRep)).2
  have hk := (ZFSet.pair_mem_prod.1 (h.representatives.1 secondRep)).2
  have ha := (ZFSet.pair_mem_prod.1 (seed.sources.1 source)).2
  obtain ⟨product, productEntry, _⟩ := h.group.mul_function.2 (ZFSet.pair δ g)
    (ZFSet.pair_mem_prod.2 ⟨hδ, hg⟩)
  have hp := (ZFSet.pair_mem_prod.1 (h.group.mul_function.1 productEntry)).2
  have agree := state.agreement product hp k hk a ha
    (seed.productAgreement δ i j g k product a transport source firstRep secondRep productEntry)
  have hy := (ZFSet.pair_mem_prod.1 (h.action.function.1 first)).2
  obtain ⟨w, acted, _⟩ := h.action.function.2 (ZFSet.pair δ y)
    (ZFSet.pair_mem_prod.2 ⟨hδ, hy⟩)
  have composed := h.action.mul δ hδ g hg product hp x hx y hy w
    (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2 productEntry first acted
  have equal := agree.entry_eq h.action hk hx below composed second
  exact equal ▸ acted

end RecursiveCompressionInvariant

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction
open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T) (M : TransitiveGround.{u})

include s in
theorem exists_groundSuccessor
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (compatible : RecursiveRepresentativeCompatibility h T)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.nextActionGraph T ∈ M.sets ∧
      PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T) ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∃ nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
        G m inv one (h.nextActionGraph T), CodedRecursiveTaskAction nextInputs T := by
  obtain ⟨next, hC, hrC, hμC, meet, graph, graphFunction, ground, family, entries, _⟩ :=
    h.exists_groundLiftEmbeddings M pairing unions powers separation hI hJ hD hrD
      hQs hrs hμs hAs hEs hFs hSs hMaps hSources hReps hG hA
  obtain ⟨hL, _, _, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hD hrD hJ hQs hrs hμs hAs hEs hFs
  have nextAction := s.nextAction_code M next
  have nextInputs := h.nextMapInputs_of_family M next family entries nextAction
  exact ⟨next, hC, hrC, hμC, meet,
    h.nextActionGraph_mem M pairing unions powers separation hI hJ hD hL
      hQs hrs hAs hFs hSources hG hA hT,
    nextAction, graph, graphFunction, ground, entries,
    nextInputs, s.nextTaskAction_of_family M next compatible entries nextInputs⟩

end PartitionPilot.Forcing.CodedRecursiveTaskAction



namespace PartitionPilot.Forcing.RecursiveCompressionInvariant

universe u
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include state s in
theorem nextAgreement {g k v : ZFSet.{u}} (hg : g ∈ G) (hk : k ∈ G) (hv : v ∈ P0)
    (agree : ActionAgreementBelow P0 r0 A0 g k v) :
    ActionAgreementBelow next.batchCarrier next.batchOrder (h.nextActionGraph T) g k v := by
  let positive : ZFSet.{u} → Prop := fun i => ∃ F, ZFSet.pair i F ∈ Filters ∧ v ∈ F
  apply s.nextAction_agreement M next ⟨g, hg⟩ ⟨k, hk⟩
    ⟨τ, state.originalSubset seed.top_mem⟩ state.top ⟨v, state.originalSubset hv⟩ positive
  · intro i S a cap base w mapEntry source capEntry baseEntry notPositive meet
    let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, h.maps.pair_source mapEntry⟩
    exact state.negative i S a (seed.filters.value index) cap base v w
      mapEntry source (seed.filters.value_entry index) capEntry baseEntry hv
      (fun member => notPositive ⟨seed.filters.value index, seed.filters.value_entry index, member⟩) meet
  · exact state.agreement g hg k hk v hv agree
  · intro i j k pos first second
    obtain ⟨F, entry, member⟩ := pos
    exact seed.positiveAgreement _ _ v i j k F agree entry member first second

include state in
theorem nextNegative
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    {i S a F cap base v w : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ h.groundLiftFamily M next)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair i F ∈ Filters)
    (capEntry : ZFSet.pair τ cap ∈ S) (baseEntry : ZFSet.pair a base ∈ S)
    (hv : v ∈ P0) (negative : v ∉ F)
    (meet : ZFSet.pair (ZFSet.pair cap v) w ∈ next.batchMeetGraph) :
    ZFSet.pair w base ∈ next.batchOrder := by
  obtain ⟨hi, rfl⟩ := (entries i S).1 mapEntry
  let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have oldMap := h.maps.value_entry index
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have oldCap := (h.liftSection_old_iff M next oldMap (state.originalSubset seed.top_mem)).1 capEntry
  have oldBase := (h.liftSection_old_iff M next oldMap ha).1 baseEntry
  have embedding := h.valid i (h.maps.value index) oldMap
  exact h.negative_cap_persists M next
    (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 oldCap)).2
    (d.original_carrier_subset state.originalSubset hv)
    (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 oldBase)).2
    (fun z entry => state.negative i (h.maps.value index) a F cap base v z
      oldMap source filter oldCap oldBase hv negative entry) meet

include state s in
theorem nextInvariant
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : RecursiveCompressionInvariant seed nextInputs where
  originalSubset := d.original_carrier_subset state.originalSubset
  originalOrder := fun _ hx _ hy => d.original_order_iff state.originalSubset state.originalOrder hx hy
  originalMeet := fun _ hx _ hy _ => d.original_meet_iff state.originalSubset state.originalMeet hx hy
  originalAction := fun _ _ hx _ => h.nextAction_original_iff state.originalSubset state.originalAction hx
  top := d.coding.greatest_preserved (state.originalSubset seed.top_mem) state.top
  agreement := fun _ hg _ hk _ hv agree => state.nextAgreement s M next hg hk hv agree
  negative := fun _ _ _ _ _ _ _ _ mapEntry source filter capEntry baseEntry hv negative meet =>
    state.nextNegative M next entries mapEntry source filter capEntry baseEntry hv negative meet

end PartitionPilot.Forcing.RecursiveCompressionInvariant



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure RecursiveGroundFields (M : TransitiveGround.{u})
    {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : Prop where
  carrier : D ∈ M.sets
  order : rD ∈ M.sets
  meet : μD ∈ M.sets
  indices : J ∈ M.sets
  spaces : Qs ∈ M.sets
  relations : rs ∈ M.sets
  meets : μs ∈ M.sets
  anchors : As ∈ M.sets
  embeddings : Es ∈ M.sets
  filters : Fs ∈ M.sets
  separators : Ss ∈ M.sets
  maps : Maps ∈ M.sets
  action : A ∈ M.sets

namespace RecursiveGroundFields
variable {M : TransitiveGround.{u}}
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (ground : RecursiveGroundFields M h)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include ground pairing unions powers separation

theorem current_codes : d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧
    d.batchMeetGraph ∈ M.sets := by
  obtain ⟨hL, hrL, hμL, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d ground.carrier ground.order ground.indices
      ground.spaces ground.relations ground.meets ground.anchors ground.embeddings ground.filters
  exact ⟨hL, hrL, hμL⟩

theorem next_fields
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    h.nextIndices ∈ M.sets ∧
    pairSecondField I J h.nextIndices Qs ∈ M.sets ∧
    pairSecondField I J h.nextIndices rs ∈ M.sets ∧
    pairSecondField I J h.nextIndices μs ∈ M.sets ∧
    pairSecondField I J h.nextIndices As ∈ M.sets ∧
    M.groundPairCompositions h.nextIndices I J (familyPointBound Qs) D d.batchCarrier Es Maps ∈ M.sets ∧
    M.groundPairPushFilters h.nextIndices I J d.batchCarrier d.batchOrder Maps Fs ∈ M.sets ∧
    recursiveSeparatorFamily h.nextIndices I J D d.batchCarrier Maps Ss ∈ M.sets := by
  obtain ⟨hL, hrL, _⟩ := ground.current_codes pairing unions powers separation
  have hK := h.nextIndices_mem M pairing unions powers separation
    hI ground.indices ground.carrier ground.filters hSources
  have fields {F : ZFSet.{u}} (hF : F ∈ M.sets) : pairSecondField I J h.nextIndices F ∈ M.sets :=
    M.pairFieldGraph_mem pairing unions powers separation false hI ground.indices hK
      (M.union_mem unions (M.union_mem unions hF)) hF
  have subset := recursiveAttachmentIndices_subset I J D Fs.sUnion.sUnion Sources Fs
  exact ⟨hK, fields ground.spaces, fields ground.relations, fields ground.meets,
    fields ground.anchors,
    (M.groundPairCompositions_spec pairing unions powers separation hK hI ground.indices
      (M.familyPointBound_mem unions ground.spaces) ground.carrier hL ground.embeddings
      ground.maps d.embeddings h.maps subset).1,
    (M.groundPairPushFilters_spec pairing unions powers separation hK hI ground.indices
      hL hrL ground.maps ground.filters h.maps d.filters subset).1,
    M.recursiveSeparatorFamily_mem pairing unions powers separation hK hI ground.indices
      ground.carrier hL ground.maps ground.separators⟩

theorem next_codes (next : h.NextInputs M)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets := by
  obtain ⟨hL, hrL, _⟩ := ground.current_codes pairing unions powers separation
  obtain ⟨hK, hQs, hrs, hμs, hAs, hEs, hFs, _⟩ :=
    ground.next_fields pairing unions powers separation hI hSources
  obtain ⟨hC, hrC, hμC, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation next hL hrL hK hQs hrs hμs hAs hEs hFs
  exact ⟨hC, hrC, hμC⟩

theorem next (next : h.NextInputs M)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T))
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : RecursiveGroundFields M inputs := by
  obtain ⟨hL, hrL, hμL⟩ := ground.current_codes pairing unions powers separation
  obtain ⟨hK, hQs, hrs, hμs, hAs, hEs, hFs, hSs⟩ :=
    ground.next_fields pairing unions powers separation hI hSources
  obtain ⟨hC, _, _⟩ := ground.next_codes pairing unions powers separation next hI hSources
  have maps := (h.groundLiftFamily_spec M pairing unions powers separation next
    hI ground.indices ground.carrier hL hC ground.spaces ground.relations ground.anchors
      ground.maps hSources ground.filters hReps hG ground.action).2.1
  have action := h.nextActionGraph_mem M pairing unions powers separation
    hI ground.indices ground.carrier hL ground.spaces ground.relations ground.anchors
      ground.filters hSources hG ground.action hT
  exact ⟨hL, hrL, hμL, hK, hQs, hrs, hμs, hAs, hEs, hFs, hSs, maps, action⟩

end RecursiveGroundFields

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RecursiveCompressionInvariant
open SetFormula
universe u
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (state : RecursiveCompressionInvariant seed h) (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u})
include state s

theorem exists_groundNext
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : RecursiveGroundFields M h)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ next : h.NextInputs M,
      ∃ nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
        G m inv one (h.nextActionGraph T),
        CodedRecursiveTaskAction nextInputs T ∧ RecursiveCompressionInvariant seed nextInputs ∧
        RecursiveGroundFields M nextInputs := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, nextInputs, nextTask⟩ :=
    s.exists_groundSuccessor M pairing unions powers separation (state.compatible s)
      hI ground.indices ground.carrier ground.order ground.spaces ground.relations ground.meets
      ground.anchors ground.embeddings ground.filters ground.separators ground.maps
      hSources hReps hG ground.action hT
  exact ⟨next, nextInputs, nextTask, state.nextInvariant s M next entries nextInputs,
    ground.next pairing unions powers separation next nextInputs hI hSources hReps hG hT⟩

end PartitionPilot.Forcing.RecursiveCompressionInvariant

end OAI
