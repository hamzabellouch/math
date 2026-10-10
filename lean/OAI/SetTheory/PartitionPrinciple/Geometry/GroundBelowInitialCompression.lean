import OAI.SetTheory.PartitionPrinciple.Forcing.GroundUnionSizeWitnesses
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompressionOrigin

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation choice

theorem sUnion {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    GroundBelow M R.sUnion K := by
  obtain ⟨D, hD, witness⟩ := M.regular_union_embeds_product
    pairing unions powers separation choice hR hK ordinal regular indices small
  have hDM := M.transitive hK hD
  have smallD := GroundBelow.of_member pairing unions powers separation hK hD
  have product := GroundBelow.product pairing unions powers separation hR hDM hK ordinal strong indices smallD
  exact product.of_embeddable pairing unions powers separation (M.union_mem unions hR)
    (M.prod_mem pairing unions powers separation hR hDM) hK witness

theorem indexed_sUnion {I Q F K : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQ : Q ∈ M.sets) (hF : F ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M I K) (family : ZFSet.IsFunc I Q F)
    (small : ∀ i A, ZFSet.pair i A ∈ F → GroundBelow M A K) :
    GroundBelow M (relationImage I Q F).sUnion K := by
  have hR := M.relationImage_mem separation hI hQ hF
  have indexImage := indices.function_image pairing unions powers separation choice hI hQ hK hF family
  apply GroundBelow.sUnion pairing unions powers separation choice hR hK ordinal regular strong indexImage
  intro A hA
  obtain ⟨_, i, _, entry⟩ := (mem_relationImage I Q F A).1 hA
  exact small i A entry

end GroundBelow

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

theorem of_countable {A : ZFSet.{u}} (omega : ZFSet.omega ∈ K)
    (small : M.groundEmbeddable A ZFSet.omega) : GroundBelow M A K := ⟨ZFSet.omega, omega, small⟩

include pairing unions powers separation infinite

theorem singleton {a : ZFSet.{u}} (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ha : a ∈ M.sets) : GroundBelow M ({a} : ZFSet.{u}) K := by
  have hEmpty := M.empty_mem ⟨K, hK⟩
  apply of_countable omega
  simpa using M.groundEmbeddable_insert pairing unions powers separation infinite hEmpty ha
    (M.empty_groundEmbeddable ZFSet.omega ⟨K, hK⟩)

theorem unorderedPair {a b : ZFSet.{u}} (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ha : a ∈ M.sets) (hb : b ∈ M.sets) : GroundBelow M ({a, b} : ZFSet.{u}) K := by
  have hEmpty := M.empty_mem ⟨K, hK⟩
  have first := M.groundEmbeddable_insert pairing unions powers separation infinite hEmpty hb
    (M.empty_groundEmbeddable ZFSet.omega ⟨K, hK⟩)
  have ground := M.insert_mem pairing unions hb hEmpty
  apply of_countable omega
  simpa using M.groundEmbeddable_insert pairing unions powers separation infinite ground ha first

include choice

theorem binary_union {A B : ZFSet.{u}}
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) : GroundBelow M (A ∪ B) K := by
  have result := sUnion pairing unions powers separation choice (M.unorderedPair_mem pairing hA hB) hK
    ordinal regular strong (unorderedPair pairing unions powers separation infinite hK omega hA hB)
    (fun X hX => (ZFSet.mem_pair.1 hX).elim (fun equal => equal ▸ first) (fun equal => equal ▸ second))
  simpa only [ZFSet.sUnion_pair] using result

theorem insert {A a : ZFSet.{u}}
    (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (small : GroundBelow M A K) : GroundBelow M (Insert.insert a A) K := by
  have hs : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have result := binary_union pairing unions powers separation infinite choice hs hA hK omega
    ordinal regular strong (singleton pairing unions powers separation infinite hK omega ha) small
  have equal : ({a} : ZFSet.{u}) ∪ A = Insert.insert a A := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
  exact equal ▸ result

end GroundBelow

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation choice

theorem indexedAttachmentDomain {I Qs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (family : FunctionGraphOn I Qs) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M (Forcing.indexedAttachmentDomain I Qs) K := by
  have hBound := M.union_mem unions (M.union_mem unions hQs)
  have hRange := M.relationImage_mem separation hI hBound hQs
  have points := GroundBelow.indexed_sUnion pairing unions powers separation choice hI hBound hQs hK
    ordinal regular strong indices family.to_isFunc templates
  have small := GroundBelow.product pairing unions powers separation hI (M.union_mem unions hRange)
    hK ordinal strong indices points
  apply small.restrict separation (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs) hK
  intro z hz
  obtain ⟨i, hi, q, rfl, Q, entry, hq⟩ := (mem_indexedAttachmentDomain I Qs z).1 hz
  exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.mem_sUnion.2
    ⟨Q, (mem_relationImage I Qs.sUnion.sUnion Qs Q).2
      ⟨pair_second_mem_doubleUnion entry, i, hi, entry⟩, hq⟩⟩

theorem indexedAttachmentFresh {I Qs rs As : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (family : FunctionGraphOn I Qs) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M (Forcing.indexedAttachmentFresh I Qs rs As) K :=
  (GroundBelow.indexedAttachmentDomain pairing unions powers separation choice hI hQs hK
    ordinal regular strong family indices templates).restrict separation
      (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs) hK
      (indexedAttachmentFresh_subset I Qs rs As)

variable (infinite : Realize M.sets infinity Fin.elim0)
include infinite

theorem taggedExtension {P N : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (old : GroundBelow M P K) (fresh : GroundBelow M N K) :
    GroundBelow M (Forcing.taggedExtension P N) K := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact GroundBelow.binary_union pairing unions powers separation infinite choice hP
    (M.prod_mem pairing unions powers separation hSingle hN) hK omega ordinal regular strong old
    (GroundBelow.product pairing unions powers separation hSingle hN hK ordinal strong
      (GroundBelow.singleton pairing unions powers separation infinite hK omega hP) fresh)

theorem batchCarrier {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (old : GroundBelow M P K) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M d.batchCarrier K :=
  GroundBelow.taggedExtension pairing unions powers separation choice infinite hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    hK omega ordinal regular strong old
    (GroundBelow.indexedAttachmentFresh pairing unions powers separation choice hI hQs hrs hAs hK
      ordinal regular strong d.spaces indices templates)

end GroundBelow

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem currentCarrier_below {P r μ K : ZFSet.{u}}
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) : GroundBelow M state.data.currentCarrier K := by
  apply GroundBelow.batchCarrier pairing unions powers separation choice infinite state.batch
    state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations state.ground.anchors
    hK conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 old indices
  intro i Q entry
  obtain rfl := ((constant.space_entry_iff i Q).1 entry).2
  exact templates

theorem canonical_iterate_below
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) (tasks : GroundBelow M I K) (n : Nat) :
    GroundBelow M (state.data.iterate M I Sources Reps G T n).D K ∧
      GroundBelow M (state.data.iterate M I Sources Reps G T n).J K := by
  induction n with
  | zero => exact ⟨old, indices⟩
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid
      pairing unions powers separation hI hSources hReps hG hT n
    have currentOld : GroundBelow M current.data.D K := by rw [equal]; exact ih.1
    have currentIndices : GroundBelow M current.data.J K := by rw [equal]; exact ih.2
    have currentConstant : RecursiveTemplateConstancy P r μ current.data := by
      rw [equal]
      exact constant.iterate M I Sources Reps G T n
    rw [RecursiveStateData.iterate_succ, ← equal]
    change GroundBelow M current.data.currentCarrier K ∧
      GroundBelow M (recursiveAttachmentIndices I current.data.J current.data.D
        current.data.Fs.sUnion.sUnion Sources current.data.Fs) K
    refine ⟨current.currentCarrier_below pairing unions powers separation infinite choice
      hK conditions currentConstant templates currentOld currentIndices, ?_⟩
    have bound := GroundBelow.product pairing unions powers separation hI current.ground.indices hK
      conditions.1 conditions.2.2.2 tasks currentIndices
    exact bound.restrict separation
      (M.recursiveAttachmentIndices_mem pairing unions powers separation hI current.ground.indices
        current.ground.carrier (M.union_mem unions (M.union_mem unions current.ground.filters))
        hSources current.ground.filters) hK (recursiveAttachmentIndices_subset _ _ _ _ _ _)

theorem canonical_currentCarrier_below
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) (tasks : GroundBelow M I K) (n : Nat) :
    GroundBelow M (state.data.iterate M I Sources Reps G T n).currentCarrier K :=
  (state.canonical_iterate_below pairing unions powers separation infinite choice
    hI hSources hReps hG hT hK conditions constant templates old indices tasks (n + 1)).1

end GroundCompressionState

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (conditions : GroundInaccessibleConditions M K)
    (points : GroundBelow M P K) (labels : GroundBelow M Labels K) :
    GroundBelow M (M.initialCompressionData P G r μ A Labels).currentCarrier K := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hSources : Sources ∈ M.sets := (fields 0).1
  have indices := M.groundEligibleTasks_below pairing unions powers separation
    hP hG hr hμ hA hLabels hK meet conditions.1 conditions.2.2.2 points labels
  have fresh : GroundBelow M
      (indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r) Sources) K := by
    apply GroundBelow.indexedAttachmentFresh pairing unions powers separation choice hI hQs hrs hSources hK
      conditions.1 conditions.2.2.1 conditions.2.2.2
      ⟨_, constantFamilyGraph_function I P⟩ indices
    intro i Q entry
    obtain rfl := ((pair_mem_constantFamilyGraph I P i Q).1 entry).2
    exact points
  exact GroundBelow.taggedExtension pairing unions powers separation choice infinite hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hSources)
    hK conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 points fresh

end TransitiveGround

open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem history_field_union_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K history U : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hHistory : history ∈ M.sets) (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) (small : ∀ n, GroundBelow M ((states n).field j) K)
    (code : NatUnionCode (fun n => (states n).field j) U) : GroundBelow M U K := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨family, hFamily, function, actual⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory states entries j
  have hBound := M.union_mem unions (M.union_mem unions hFamily)
  have sizes : ∀ i A, ZFSet.pair i A ∈ family → GroundBelow M A K := by
    intro i A entry
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 (function.pair_source entry)
    rw [(actual n A).1 entry]
    exact small n
  have bound := GroundBelow.indexed_sUnion pairing unions powers separation choice hOmega hBound hFamily hK
    conditions.1 conditions.2.2.1 conditions.2.2.2
    (GroundBelow.of_member pairing unions powers separation hK conditions.2.1) function.to_isFunc sizes
  have same : U = (relationImage ZFSet.omega family.sUnion.sUnion family).sUnion := by
    apply ZFSet.ext
    intro x
    rw [code x, ZFSet.mem_sUnion]
    constructor
    · rintro ⟨n, hx⟩
      have entry := (actual n ((states n).field j)).2 rfl
      exact ⟨(states n).field j,
        (mem_relationImage _ _ _ _).2
          ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩, hx⟩
    · rintro ⟨A, hA, hx⟩
      obtain ⟨_, i, hi, entry⟩ := (mem_relationImage _ _ _ _).1 hA
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
      refine ⟨n, ?_⟩
      change x ∈ (states n).field j
      exact (actual n A).1 entry ▸ hx
  exact same.symm ▸ bound

end TransitiveGround

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem union_below (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) (tasks : GroundBelow M I K) :
    GroundBelow M (data.fields 0) K := by
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  exact M.history_field_union_below pairing unions powers separation collection infinite choice
    hK conditions hHistory (state.data.iterate M I Sources Reps G T) entries 0
    (fun n => (state.canonical_iterate_below pairing unions powers separation infinite choice
      hI hSources hReps hG hT hK conditions constant templates old indices tasks n).1)
    (data.fieldUnion 0)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_below (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ initial)
    (templates : GroundBelow M P K) (old : GroundBelow M initial.D K)
    (indices : GroundBelow M initial.J K) (tasks : GroundBelow M I K) :
    GroundBelow M (data.fields 0) K := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_below data pairing unions powers separation collection infinite choice
    hI hSources hReps hG hT hK conditions constant templates old indices tasks

end GroundCompressionOrigin

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem initialCompressionUnion_below
    {P G r μ A Labels τ Sources Reps m inv one T Filters K : ZFSet.{u}}
    (origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
      P r μ A τ (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m inv one T Filters)
    (data : GroundCompressionUnionData M (M.initialCompressionData P G r μ A Labels)
      (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (conditions : GroundInaccessibleConditions M K)
    (points : GroundBelow M P K) (labels : GroundBelow M Labels K) :
    GroundBelow M (data.fields 0) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have tasks := M.groundEligibleTasks_below pairing unions powers separation
    hP hG hr hμ hA hLabels hK meet conditions.1 conditions.2.2.2 points labels
  exact origin.union_below data pairing unions powers separation collection infinite choice
    hI hSources hReps hG hT hK conditions
    (M.initialCompressionData_template_constancy P G r μ A Labels) points points tasks tasks

end TransitiveGround

end PartitionPilot.Forcing

end OAI
