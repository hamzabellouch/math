import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionUnionBaseFilling

namespace OAI

namespace PartitionPilot.Forcing

namespace AttachmentBatchInputs
universe u
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem original_positive_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {p : ZFSet.{u} // p ∈ P} ⊕ d.templates.Fresh) :
    (∃ f ∈ d.filter i, ZFSet.pair f (d.coding.encode x) ∈ d.batchOrder) ↔
      Positive d.templates.extension (d.templates.originalFamily i) x := by
  constructor
  · rintro ⟨f, hf, lower⟩
    let old : {p : ZFSet.{u} // p ∈ P} := ⟨f, (d.fiber i).filter.subset hf⟩
    exact ⟨.inl old, hf, (d.coding.le_encode (.inl old) x).1 lower⟩
  · rintro ⟨f, hf, lower⟩
    cases f with
    | inl f => exact ⟨f.val, hf, (d.coding.le_encode (.inl f) x).2 lower⟩
    | inr f => exact False.elim hf

theorem initial_cap_profile (i : {i : ZFSet.{u} // i ∈ I}) (t : d.templates.Space i)
    (top : ∀ y, (d.templates.order i).le y t)
    (outside : ¬ (d.templates.order i).le t (d.templates.anchor i)) :
    let cap := d.coding.encode (.inr (d.templates.cap i t outside))
    CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.templates.base i).val (d.separator i) cap (d.filter i) ∧
    ZFSet.pair (d.templates.base i).val cap ∈ d.batchOrder ∧
    ZFSet.pair cap (d.templates.base i).val ∉ d.batchOrder ∧
    ZFSet.pair (d.separator i) cap ∉ d.batchOrder := by
  dsimp only
  have profile := d.templates.initial_profile i t top outside
  have strict := d.templates.cap_strict_above_base i t top outside
  have separated := d.templates.separator_not_below_cap i t top outside
  refine ⟨?_, (d.coding.le_encode _ _).2 strict.1,
    fun lower => strict.2 ((d.coding.le_encode _ _).1 lower),
    fun lower => separated ((d.coding.le_encode _ _).1 lower)⟩
  intro v hv above
  obtain ⟨x, rfl⟩ := d.coding.encode_surjective v hv
  have aboveTyped := (d.coding.le_encode (.inl (d.templates.separator i)) x).1 above
  have result := profile x aboveTyped
  constructor
  · intro positive
    exact (d.coding.le_encode _ _).2 (result.1 ((d.original_positive_iff i x).1 positive))
  · intro negative
    have equal := result.2 (fun positive => negative ((d.original_positive_iff i x).2 positive))
    have entry := d.coding.encoded_meet_entry (.inr (d.templates.cap i t outside)) x
    rw [equal] at entry
    exact entry

end AttachmentBatchInputs

section
universe u

namespace AttachmentBatchInputs
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}

theorem fresh_shadow_separation
    (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)
    (i j : {i : ZFSet.{u} // i ∈ I}) {q t b c : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j))
    (different : i ≠ j)
    (hb : ZFSet.pair (ZFSet.pair i.val q) b ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (hc : ZFSet.pair (ZFSet.pair j.val t) c ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) c ∈ d.batchOrder ∨
    ZFSet.pair (ZFSet.pair P (ZFSet.pair j.val t)) b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t))) z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b c) z ∈ d.batchMeetGraph := by
  classical
  have bP := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 hb)).2
  have cP := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 hc)).2
  by_cases first : c ∈ d.filter i
  · exact Or.inl ((d.batch_old_upper_iff i hq cP).2 first)
  by_cases second : b ∈ d.filter j
  · exact Or.inr (Or.inl ((d.batch_old_upper_iff j ht bP).2 second))
  have notIJ := fun lower => first ((d.batch_cross_lower_iff i j hq ht different hc).1 lower)
  have notJI := fun lower => second ((d.batch_cross_lower_iff j i ht hq different.symm hb).1 lower)
  let x : {p : ZFSet.{u} // p ∈ P} := ⟨b, bP⟩
  let y : {p : ZFSet.{u} // p ∈ P} := ⟨c, cP⟩
  refine Or.inr (Or.inr ⟨(d.oldOrder.toMeetOrder.meet x y).val, ?_, ?_⟩)
  · exact d.batch_cross_meet_code i j hq ht different hb hc
      (d.oldOrder.toMeetOrder_meet_entry x y) notIJ notJI
  · exact d.old_meet_entry (d.oldOrder.toMeetOrder_meet_entry x y)

end AttachmentBatchInputs

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (meet : MeetOrderCode P r μ) (hT : T ∈ P) (top : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT top

theorem groundEligibleTask_old_below_cap_iff {i c v : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) (hv : v ∈ P) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair v (eligibleTaskCap P T i) ∈ d.batchOrder ↔ ZFSet.pair v c ∈ d.batchOrder := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have hq := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have shadow := M.groundEligibleTask_cap_shadow meet hT top hi target
  have hc := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 shadow)).2
  exact (d.batch_old_lower_iff j hq hv shadow).trans
    (d.coding.le_encode (.inl ⟨v, hv⟩) (.inl ⟨c, hc⟩)).symm

theorem groundEligibleTask_cap_separation {i j b c : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (hj : j ∈ M.groundEligibleTasks P G r μ A Labels) (different : i ≠ j)
    (targetI : ZFSet.pair i b ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair (eligibleTaskCap P T i) c ∈ d.batchOrder ∨
    ZFSet.pair (eligibleTaskCap P T j) b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair (eligibleTaskCap P T i) (eligibleTaskCap P T j)) z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b c) z ∈ d.batchMeetGraph := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let k : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let l : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
  have freshI := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have freshJ := M.groundEligibleTask_cap_fresh group action meet hT top hj
  have hq := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry k) (d.rel_entry k) (d.anchor_entry k)).1 freshI
  have ht := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry l) (d.rel_entry l) (d.anchor_entry l)).1 freshJ
  exact d.fresh_shadow_separation k l hq ht (fun equal => different (congrArg Subtype.val equal))
    (M.groundEligibleTask_cap_shadow meet hT top hi targetI)
    (M.groundEligibleTask_cap_shadow meet hT top hj targetJ)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem groundInitialMap_cap_base_values {i S a c K b : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S →
    K = eligibleTaskCap P T i ∧ b = c := by
  dsimp only
  intro indexed source target cap base
  obtain ⟨function, capEntry, baseEntry⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels group action meet hT top
    indexed source target
  let graph : FunctionGraphOn P S := ⟨_, function⟩
  exact ⟨graph.unique cap capEntry, graph.unique base baseEntry⟩

theorem groundInitialMap_old_below_cap_iff {i S a c K b v : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S → v ∈ P →
    (ZFSet.pair v K ∈ d.batchOrder ↔ ZFSet.pair v b ∈ d.batchOrder) := by
  dsimp only
  intro indexed source target cap base hv
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed source target cap base
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  rw [capEq, baseEq]
  exact M.groundEligibleTask_old_below_cap_iff group action meet hT top hi target hv

theorem groundInitialMap_cap_separation {i j S V a a' c c' K K' b b' : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair j V ∈ Maps →
    ZFSet.pair i a ∈ As → ZFSet.pair j a' ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair j c' ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair T K' ∈ V →
    ZFSet.pair a b ∈ S → ZFSet.pair a' b' ∈ V → i ≠ j →
    ZFSet.pair K b' ∈ d.batchOrder ∨ ZFSet.pair K' b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair K K') z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b b') z ∈ d.batchMeetGraph := by
  dsimp only
  intro indexed indexed' source source' target target' cap cap' base base' different
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed source target cap base
  obtain ⟨capEq', baseEq'⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed' source' target' cap' base'
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  have hj := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source').1).1
  rw [capEq, capEq', baseEq, baseEq']
  exact M.groundEligibleTask_cap_separation group action meet hT top hi hj different target target'

end TransitiveGround
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (meet : MeetOrderCode P r μ) (hT : T ∈ P) (top : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT top

theorem groundEligibleTask_initial_profile {i c e F : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (separator : ZFSet.pair i e ∈ literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    c ∈ P ∧ e ∈ P ∧ eligibleTaskCap P T i ∈ d.batchCarrier ∧ F ⊆ P ∧ F.Nonempty ∧
      CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph c e (eligibleTaskCap P T i) F ∧
      ZFSet.pair c (eligibleTaskCap P T i) ∈ d.batchOrder ∧
      ZFSet.pair (eligibleTaskCap P T i) c ∉ d.batchOrder ∧
      ZFSet.pair e (eligibleTaskCap P T i) ∉ d.batchOrder := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
  have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have freshT := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have parts := (mem_freshPart _ _ _ T).1 freshT
  let t : d.templates.Space j := ⟨T, parts.1⟩
  have outside : ¬ (d.templates.order j).le t (d.templates.anchor j) := parts.2
  have greatest : ∀ y, (d.templates.order j).le y t := by
    intro y
    change ZFSet.pair y.val T ∈ d.rel j
    rw [relEq]
    have hy : y.val ∈ d.space j := y.property
    exact top y.val (by simpa only [spaceEq] using hy)
  let cap := d.templates.cap j t outside
  have shadow : ZFSet.pair (d.freshCode cap) c ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
        (literalTaskBaseGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :=
    M.groundEligibleTask_cap_shadow meet hT top hi target
  have baseEq : (d.templates.base j).val = c := by
    have equal := d.freshCode_shadow_value cap c shadow
    change c = (d.templates.shadow (d.templates.cap j t outside)).val at equal
    rw [d.templates.cap_shadow j t greatest outside] at equal
    exact equal.symm
  have separatorEq : d.separator j = e := d.separators.unique (d.separator_entry j) separator
  have filterEq : d.filter j = F := d.filters.unique (d.filter_entry j) filter
  have hcP : c ∈ P := baseEq ▸ (d.templates.base j).property
  have heP : e ∈ P := separatorEq ▸ (d.fiber j).separator_mem
  have filterSubset : F ⊆ P := filterEq ▸ (d.fiber j).filter.subset
  have nonempty : F.Nonempty := filterEq ▸ (d.fiber j).filter.nonempty
  refine ⟨hcP, heP, M.groundEligibleTask_cap_mem group action meet hT top hi,
    filterSubset, nonempty, ?_⟩
  have laws := d.initial_cap_profile j t greatest outside
  have capEq : d.coding.encode (.inr (d.templates.cap j t outside)) = eligibleTaskCap P T i := rfl
  simpa only [baseEq, separatorEq, filterEq, capEq] using laws

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem groundInitialMap_profile {i S a c e F K b : ZFSet.{u}} :
    let initial := M.initialCompressionData P G r μ A Labels
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair i S ∈ initial.Maps →
    ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair i e ∈ literalTaskSeparatorGraph I P R U Labels →
    ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S →
      b = c ∧ b ∈ initial.currentCarrier ∧ e ∈ initial.currentCarrier ∧ K ∈ initial.currentCarrier ∧
      F ⊆ initial.currentCarrier ∧ F.Nonempty ∧
      CodedInsertionProfile initial.currentCarrier initial.currentOrder initial.currentMeet b e K F ∧
      ZFSet.pair b K ∈ initial.currentOrder ∧ ZFSet.pair K b ∉ initial.currentOrder ∧
      ZFSet.pair e K ∉ initial.currentOrder := by
  dsimp only
  intro indexed source target separator filter cap base
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values group action meet hT top
    pairing unions powers separation hP hG hr hμ hA hLabels indexed source target cap base
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  refine ⟨baseEq, ?_⟩
  rw [capEq, baseEq]
  obtain ⟨hcP, heP, hk, subset, nonempty, laws⟩ :=
    M.groundEligibleTask_initial_profile group action meet hT top hi target separator filter
  exact ⟨old_mem_taggedExtension hcP, old_mem_taggedExtension heP, hk,
    fun _ hf => old_mem_taggedExtension (subset hf), nonempty, laws⟩

end TransitiveGround

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_profile {c e K F : ZFSet.{u}}
    (hc : c ∈ state.data.currentCarrier) (he : e ∈ state.data.currentCarrier)
    (hK : K ∈ state.data.currentCarrier) (subset : F ⊆ state.data.currentCarrier)
    (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile state.data.currentCarrier state.data.currentOrder
      state.data.currentMeet c e K F)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) :
    CodedInsertionProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F :=
  data.currentOrder.insertionProfile data.currentMeet
    (fun n => (state.canonical_iterate_codes pairing unions powers separation
      hI hSources hReps hG hT n).2.1.order)
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).2.2.2.2.1)
    (state.canonical_iterate_profile pairing unions powers separation
      hI hSources hReps hG hT hc he hK subset nonempty profile separated)

theorem union_separator_not_below_cap {e K : ZFSet.{u}}
    (he : e ∈ state.data.currentCarrier) (hK : K ∈ state.data.currentCarrier)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) :
    ZFSet.pair e K ∉ data.fields 1 := by
  intro below
  exact separated ((state.union_order_iff data pairing unions powers separation
    hI hSources hReps hG hT 1 he hK).1 below)

end GroundCompressionState

section
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem union_input_capProfile
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {c e K F : ZFSet.{u}}
    (profile : CodedCapProfile state.data.D state.data.rD state.data.μD c e K F) :
    CodedCapProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F := by
  have hc : c ∈ state.data.currentCarrier := old_mem_taggedExtension profile.target_mem
  have he : e ∈ state.data.currentCarrier := old_mem_taggedExtension profile.separator_mem
  have hK : K ∈ state.data.currentCarrier := old_mem_taggedExtension profile.cap_mem
  have subset : F ⊆ state.data.currentCarrier := fun _ hf => old_mem_taggedExtension (profile.filter_subset hf)
  have first := state.batch.insertion_profile_persists profile.target_mem profile.separator_mem
    profile.cap_mem profile.filter_subset profile.nonempty profile.profile profile.separator_not_below_cap
  have separated : ZFSet.pair e K ∉ state.data.currentOrder := by
    intro lower
    exact profile.separator_not_below_cap
      ((state.batch.old_order_iff profile.separator_mem profile.cap_mem).1 lower)
  refine ⟨(data.fieldUnion 0).subset 0 profile.target_mem,
    (data.fieldUnion 0).subset 0 profile.separator_mem,
    (data.fieldUnion 0).subset 0 profile.cap_mem,
    fun _ hf => (data.fieldUnion 0).subset 0 (profile.filter_subset hf), profile.nonempty,
    state.union_profile data pairing unions powers separation hI hSources hReps hG hT
      hc he hK subset profile.nonempty first separated, ?_, ?_, ?_⟩
  · exact (state.union_order_iff data pairing unions powers separation hI hSources hReps hG hT
      0 profile.target_mem profile.cap_mem).2 profile.target_below_cap
  · intro lower
    exact profile.cap_not_below_target ((state.union_order_iff data pairing unions powers separation
      hI hSources hReps hG hT 0 profile.cap_mem profile.target_mem).1 lower)
  · intro lower
    exact profile.separator_not_below_cap ((state.union_order_iff data pairing unions powers separation
      hI hSources hReps hG hT 0 profile.separator_mem profile.cap_mem).1 lower)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_input_capProfile
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {c e K F : ZFSet.{u}} (profile : CodedCapProfile initial.D initial.rD initial.μD c e K F) :
    CodedCapProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_input_capProfile data pairing unions powers separation
    hI hSources hReps hG hT profile

end GroundCompressionOrigin
end

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable {seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels hI hSources hReps hT

theorem union_initial_profile
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a c e F K : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (separator : ZFSet.pair i e ∈ literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ K ∈ f) :
    CodedCapProfile (algebra.union.fields 0) (algebra.union.fields 1) (algebra.union.fields 2) c e K F := by
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have haD : a ∈ state.data.D := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using ha
  have hτD : τ ∈ state.data.D := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using seed.top_mem
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  obtain ⟨b, base, _⟩ := (state.inputs.valid i old oldEntry).injection.function.2 a haD
  have capOld := (algebra.restrict i f indexed 0 old oldEntry τ hτD K).1 cap
  have indexedOld : ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps := by
    simpa only [initialData] using oldEntry
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  obtain ⟨baseEq, hc, he, hK, subset, nonempty, profile, lower, reverse, separate⟩ :=
    M.groundInitialMap_profile state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top
      pairing unions powers separation hP hG hr hμ hA hLabels
      indexedOld source target separator filter capOld base
  subst b
  have first : CodedCapProfile state.data.currentCarrier state.data.currentOrder state.data.currentMeet c e K F := by
    rw [initialData]
    exact ⟨hc, he, hK, subset, nonempty, profile, lower, reverse, separate⟩
  refine ⟨algebra.union.currentCarrier.subset 0 first.target_mem,
    algebra.union.currentCarrier.subset 0 first.separator_mem,
    algebra.union.currentCarrier.subset 0 first.cap_mem,
    fun _ hf => algebra.union.currentCarrier.subset 0 (first.filter_subset hf), first.nonempty,
    state.union_profile algebra.union pairing unions powers separation hI hSources hReps hG hT
      first.target_mem first.separator_mem first.cap_mem first.filter_subset first.nonempty
      first.profile first.separator_not_below_cap,
    algebra.union.currentOrder.subset 0 first.target_below_cap, ?_, ?_⟩
  · intro below
    exact first.cap_not_below_target ((state.union_order_iff algebra.union pairing unions powers separation
      hI hSources hReps hG hT 1 first.cap_mem first.target_mem).1 below)
  · exact state.union_separator_not_below_cap algebra.union pairing unions powers separation
      hI hSources hReps hG hT first.separator_mem first.cap_mem first.separator_not_below_cap

theorem initial_union_profiles
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    CodedCompressionProfiles (algebra.union.fields 0) (algebra.union.fields 1) (algebra.union.fields 2)
      (algebra.caps τ)
      (literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
      (literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
      (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) := by
  intro i c e K F cap target separator filter
  have hi := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 cap)).1
  obtain ⟨f, indexed⟩ := algebra.function.total hi
  obtain ⟨a, source, _⟩ := seed.sources.2 i hi
  rw [initialSources] at source
  exact state.union_initial_profile algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData indexed source target separator filter
    ((state.union_cap_entry_iff algebra indexed).1 cap)

end GroundCompressionState

end PartitionPilot.Forcing

end OAI
