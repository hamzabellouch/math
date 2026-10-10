import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps
import OAI.SetTheory.PartitionPrinciple.Geometry.InitialCompressionUnionProfiles

namespace OAI

namespace PartitionPilot.Forcing.GroundCompressionState
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

include pairing unions powers separation hP hG hr hμ hA hLabels in
theorem initial_map_marks
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a k b : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ k ∈ f) (base : ZFSet.pair a b ∈ f) :
    ∃ old c, ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps ∧
      ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels ∧
      ZFSet.pair τ k ∈ old ∧ ZFSet.pair a b ∈ old := by
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have hi : i ∈ M.groundEligibleTasks P G r μ A Labels :=
    (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  have hτD : τ ∈ state.data.D := by
    simp only [initialData]
    exact seed.top_mem
  have haD : a ∈ state.data.D := by
    simp only [initialData]
    exact ha
  have capOld := (algebra.restrict i f indexed 0 old oldEntry τ hτD k).1 cap
  have baseOld := (algebra.restrict i f indexed 0 old oldEntry a haD b).1 base
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels seed.originalOrder
  obtain ⟨c, target, _⟩ := (fields 1).2.2 i hi
  refine ⟨old, c, ?_, target, capOld, baseOld⟩
  simpa only [initialData] using oldEntry

variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels hI hSources hReps hT

theorem union_initial_old_shadow
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a k b x : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ k ∈ f) (base : ZFSet.pair a b ∈ f) (hx : x ∈ P)
    (below : ZFSet.pair x k ∈ algebra.union.fields 1) : ZFSet.pair x b ∈ algebra.union.fields 1 := by
  obtain ⟨old, c, indexedOld, target, capOld, baseOld⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData indexed source cap base
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  obtain ⟨function, _, _⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels
    state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top indexedOld source target
  have hxCurrent : x ∈ state.data.currentCarrier := old_mem_taggedExtension (by
    simp only [initialData]
    exact hx)
  have hkCurrent : k ∈ state.data.currentCarrier := by
    simp only [initialData]
    exact (ZFSet.pair_mem_prod.1 (function.1 capOld)).2
  have finiteBelow : ZFSet.pair x k ∈ state.data.currentOrder :=
    (state.union_order_iff algebra.union pairing unions powers separation hI hSources hReps hG hT
      1 hxCurrent hkCurrent).1 below
  have initialBelow : ZFSet.pair x k ∈ (M.initialCompressionData P G r μ A Labels).currentOrder := by
    simpa only [initialData] using finiteBelow
  have result := (M.groundInitialMap_old_below_cap_iff state.inputs.group seed.originalAction
    seed.originalOrder seed.top_mem top pairing unions powers separation hP hG hr hμ hA hLabels
    indexedOld source target capOld baseOld hx).1 initialBelow
  apply algebra.union.currentOrder.subset 0
  simp only [initialData]
  exact result

omit hI hSources hReps hT in
theorem union_initial_cap_separation
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i j f g a c k l b d : ZFSet.{u}}
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j g ∈ algebra.maps)
    (firstSource : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (secondSource : ZFSet.pair j c ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (firstCap : ZFSet.pair τ k ∈ f) (secondCap : ZFSet.pair τ l ∈ g)
    (firstBase : ZFSet.pair a b ∈ f) (secondBase : ZFSet.pair c d ∈ g) (different : i ≠ j) :
    ZFSet.pair k d ∈ algebra.union.fields 1 ∨ ZFSet.pair l b ∈ algebra.union.fields 1 ∨
      ∃ z, ZFSet.pair (ZFSet.pair k l) z ∈ algebra.union.fields 2 ∧
        ZFSet.pair (ZFSet.pair b d) z ∈ algebra.union.fields 2 := by
  obtain ⟨old, target, indexedOld, targetEntry, capOld, baseOld⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData firstMap firstSource firstCap firstBase
  obtain ⟨old', target', indexedOld', targetEntry', capOld', baseOld'⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData secondMap secondSource secondCap secondBase
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  have result := M.groundInitialMap_cap_separation state.inputs.group seed.originalAction
    seed.originalOrder seed.top_mem top pairing unions powers separation hP hG hr hμ hA hLabels
    indexedOld indexedOld' firstSource secondSource targetEntry targetEntry' capOld capOld' baseOld baseOld' different
  rcases result with first | second | common
  · apply Or.inl
    apply algebra.union.currentOrder.subset 0
    simp only [initialData]
    exact first
  · apply Or.inr ∘ Or.inl
    apply algebra.union.currentOrder.subset 0
    simp only [initialData]
    exact second
  · obtain ⟨z, capsMeet, basesMeet⟩ := common
    refine Or.inr (Or.inr ⟨z, ?_, ?_⟩)
    · apply algebra.union.currentMeet.subset 0
      simp only [initialData]
      exact capsMeet
    · apply algebra.union.currentMeet.subset 0
      simp only [initialData]
      exact basesMeet

end PartitionPilot.Forcing.GroundCompressionState

namespace PartitionPilot.Forcing.GroundCompressionState
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
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem union_map_target
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a c : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    ZFSet.pair a c ∈ f := by
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  have indexedOld : ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps := by
    simpa only [initialData] using oldEntry
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  have base := (M.groundInitialMap_cap_base pairing unions powers separation
    hP hG hr hμ hA hLabels state.inputs.group seed.originalAction seed.originalOrder
    seed.top_mem top indexedOld source target).2.2
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have haD : a ∈ state.data.D := by
    simp only [initialData]
    exact ha
  exact (algebra.restrict i f indexed 0 old oldEntry a haD c).2 base

theorem union_caps_common_target_meet
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i j f g a a' c K L : ZFSet.{u}}
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j g ∈ algebra.maps)
    (sourceI : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (sourceJ : ZFSet.pair j a' ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetI : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (capI : ZFSet.pair τ K ∈ f) (capJ : ZFSet.pair τ L ∈ g) (different : i ≠ j)
    (firstStrict : ZFSet.pair K c ∉ algebra.union.fields 1)
    (secondStrict : ZFSet.pair L c ∉ algebra.union.fields 1) :
    ZFSet.pair (ZFSet.pair K L) c ∈ algebra.union.fields 2 := by
  have firstBase := state.union_map_target algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData firstMap sourceI targetI
  have secondBase := state.union_map_target algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData secondMap sourceJ targetJ
  have apart := state.union_initial_cap_separation algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData firstMap secondMap sourceI sourceJ capI capJ
    firstBase secondBase different
  rcases apart with first | second | common
  · exact False.elim (firstStrict first)
  · exact False.elim (secondStrict second)
  · obtain ⟨z, capsMeet, basesMeet⟩ := common
    have hc := (ZFSet.pair_mem_prod.1
      ((algebra.embedding i f firstMap).injection.function.1 firstBase)).2
    have hz := (ZFSet.pair_mem_prod.1 (algebra.union.meet.operation.1 basesMeet)).2
    have equal := algebra.union.meet.order.antisymm z hz c hc
      (algebra.union.meet.lower_left c c z basesMeet)
      (algebra.union.meet.greatest c c z c hc basesMeet
        (algebra.union.meet.order.refl c hc) (algebra.union.meet.order.refl c hc))
    exact equal ▸ capsMeet

end PartitionPilot.Forcing.GroundCompressionState

namespace PartitionPilot.Forcing.GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P r μ A τ I Sources Reps G m inv one T Filters)
variable (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)

include origin in
theorem union_caps_common_target_meet
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (initialData : initial = M.initialCompressionData P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    {i j c K L : ZFSet.{u}}
    (capI : ZFSet.pair i K ∈ algebra.caps τ) (capJ : ZFSet.pair j L ∈ algebra.caps τ)
    (targetI : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (different : i ≠ j) (firstStrict : ZFSet.pair K c ∉ algebra.union.fields 1)
    (secondStrict : ZFSet.pair L c ∉ algebra.union.fields 1) :
    ZFSet.pair (ZFSet.pair K L) c ∈ algebra.union.fields 2 := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  have hi := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 capI)).1
  have hj := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 capJ)).1
  obtain ⟨f, indexedI⟩ := algebra.function.total hi
  obtain ⟨g, indexedJ⟩ := algebra.function.total hj
  obtain ⟨a, sourceI, _⟩ := seed.sources.2 i hi
  obtain ⟨a', sourceJ, _⟩ := seed.sources.2 j hj
  exact state.union_caps_common_target_meet algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData indexedI indexedJ
    (initialSources ▸ sourceI) (initialSources ▸ sourceJ) targetI targetJ
    ((state.union_cap_entry_iff algebra indexedI).1 capI)
    ((state.union_cap_entry_iff algebra indexedJ).1 capJ) different firstStrict secondStrict

end PartitionPilot.Forcing.GroundCompressionOrigin

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionCompletion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        Nonempty (GroundCompressionCompletion M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  apply state.completion_of_accounting algebra pairing unions powers separation hI hSources hReps hG hT
  refine {
    original_subset := state.union_original_subset algebra.union
    base_filled := ?_
    old_shadow := ?_
    cap_separation := ?_
    fresh_accounting := ?_
  }
  · intro i hi f b indexed based x hx below
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    obtain ⟨g, representative, _⟩ := state.inputs.representatives.2 i hi
    exact state.union_map_base_filling algebra pairing unions powers separation hI hSources hReps hG hT
      indexed source representative ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi b k based capped x hx below
    obtain ⟨f, indexed⟩ := algebra.function.total hi
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    exact state.union_initial_old_shadow algebra pairing unions powers separation
      hP hG hr hμ hA hLabels hI hSources hReps hT initialData indexed source
      ((state.union_cap_entry_iff algebra indexed).1 capped)
      ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi j hj different b c k l basedI basedJ cappedI cappedJ
    obtain ⟨f, indexedI⟩ := algebra.function.total hi
    obtain ⟨g, indexedJ⟩ := algebra.function.total hj
    obtain ⟨a, sourceI, _⟩ := seed.sources.2 i hi
    obtain ⟨d, sourceJ, _⟩ := seed.sources.2 j hj
    exact state.union_initial_cap_separation algebra pairing unions powers separation
      hP hG hr hμ hA hLabels initialData indexedI indexedJ sourceI sourceJ
      ((state.union_cap_entry_iff algebra indexedI).1 cappedI)
      ((state.union_cap_entry_iff algebra indexedJ).1 cappedJ)
      ((state.union_base_entry_iff algebra indexedI sourceI).1 basedI)
      ((state.union_base_entry_iff algebra indexedJ sourceJ).1 basedJ) different
  · have initialAccounting := M.initialCompressionData_accounting pairing unions powers separation
      hP hG hr hμ hA hLabels group action meet hτ top
    rw [← initialData] at initialAccounting
    intro x hx
    rcases state.union_fresh_accounting algebra pairing unions powers separation
      hI hSources hReps hG hT initialAccounting x hx with original | fresh
    · exact Or.inl original
    · obtain ⟨i, hi, f, a, k, b, y, hy, indexed, source, cap, base, image, below, outside⟩ := fresh
      exact Or.inr ⟨i, hi, f, k, b, y, hy, indexed,
        (state.union_cap_entry_iff algebra indexed).2 cap,
        (state.union_base_entry_iff algebra indexed source).2 base, image, below, outside⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
