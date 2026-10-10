import OAI.SetTheory.PartitionPrinciple.Definability.MainPrefixTraceStepFormulas

namespace OAI

namespace PartitionPilot.Forcing

namespace OrdinalRecursionTrace
universe u
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_values {i q : ZFSet.{u}} (entry : ZFSet.pair i q ∈ p) :
    q ∈ B ∧ MainPrefixAtIndex (insert i i) q := by
  have step := trace.2 i (trace.1.pair_source entry) q entry
  exact ⟨step.1, step.2.1⟩

theorem mainPrefix_extends {i j q r : ZFSet.{u}}
    (first : ZFSet.pair i q ∈ p) (second : ZFSet.pair j r ∈ p)
    (before : i = j ∨ i ∈ j) : MainPrefixExtends q r := by
  rcases before with rfl | before
  · have equal := trace.1.unique first second
    rw [equal]
    exact (trace.mainPrefix_values second).2.refl
  · have step := trace.2 j (trace.1.pair_source second) r second
    exact step.2.2.1 i q (pair_mem_graphRestriction.2 ⟨first, before⟩)

theorem preservedMainPrefixHistory {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    PreservedMainPrefixHistoryCode M K Labels C D rD A p := by
  refine ⟨trace.1, ?_, ?_⟩
  · intro i q entry
    obtain ⟨member, S, E, equal⟩ := trace.mainPrefix_values entry
    obtain ⟨T, F, G, encoded, valid, preserved⟩ := candidates q member
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 (encoded.symm.trans equal)
    exact ⟨_, _, equal, valid, preserved⟩
  · intro i j q r first second before
    exact trace.mainPrefix_extends first second before

end OrdinalRecursionTrace

namespace PreservedMainPrefixHistoryCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem unionCode_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) :
    history.graphFamily.unionCode ∈ M.sets := by
  apply history.graphFamily.unionCode_ground pairing unions powers separation
    (@SetMembers.raw A) (SetMembers.raw_injective A)
  · rw [ordinalMainIndex_key_range]
    exact domain
  · rw [history.graphFamily_codeGraph_eq]
    exact whole

theorem ranked_union_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K))
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) (small : GroundBelow M A K)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD) :
    history.graphFamily.unionCode ∈ M.sets ∧
      ZFSet.rank history.graphFamily.unionCode < ZFSet.rank K ∧
      history.graphFamily.unionCode ∈ level.preservedMainPrefixes Labels C D rD := by
  have ranks : ∀ i, ZFSet.rank (history.graphFamily.code i) < ZFSet.rank K := by
    intro i
    exact ((level.membership _).1
      ((level.mem_preservedMainPrefixes).1 (candidates _ _ (history.graphFamily_code_entry i))).1).2
  have domainRange : ZFSet.range (@SetMembers.raw A) ∈ M.sets := by
    rw [ordinalMainIndex_key_range]
    exact domain
  have wholeFamily : familyCodeGraph (@SetMembers.raw A) history.graphFamily.code ∈ M.sets := by
    rw [history.graphFamily_codeGraph_eq]
    exact whole
  have smallRange : GroundBelow M (ZFSet.range (@SetMembers.raw A)) K := by
    rw [ordinalMainIndex_key_range]
    exact small
  have rank := history.graphFamily.unionCode_rank_lt_small pairing unions powers separation collection
    hK ordinalK regular limit (@SetMembers.raw A) (SetMembers.raw_injective A) domainRange wholeFamily smallRange ranks
  have ground := history.unionCode_ground pairing unions powers separation domain whole
  refine ⟨ground, rank, level.mem_preservedMainPrefixes.2 ⟨(level.membership _).2 ⟨ground, rank⟩, ?_⟩⟩
  exact ⟨history.graphFamily.indexUnion, history.graphFamily.stageUnion, history.graphFamily.transitionUnion,
    rfl, history.graphFamily.union_valid,
    history.graphFamily.union_profile_graph_code history.graphFamily_profiles⟩

theorem union_mem_recursionPrefixes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K))
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) (small : GroundBelow M A K)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD)
    {Omega : ZFSet.{u}} (member : A ∈ Omega) (nonempty : A ≠ ∅)
    (ordinalA : ordinalSetProperty A) :
    history.graphFamily.unionCode ∈ level.recursionPrefixes Omega Labels C D rD := by
  have candidate := (history.ranked_union_candidate pairing unions powers separation collection
    hK ordinalK regular limit domain whole small level candidates).2.2
  refine level.mem_recursionPrefixes.2 ⟨candidate, mainPrefixRecursionIndexCode_iff.2 ?_⟩
  rw [history.graphFamily_indexUnion ordinalA]
  exact ⟨member, nonempty⟩

end PreservedMainPrefixHistoryCode

section
universe u

theorem MainPrefixHistoryExtends.union_code {p q T i : ZFSet.{u}}
    (history : MainPrefixHistoryExtends p q) (code : MainPrefixAtIndex T q)
    (last : ZFSet.pair i q ∈ p) : MainPrefixHistoryUnionCode p q := by
  obtain ⟨S, E, rfl⟩ := code
  refine ⟨T, S, E, rfl, ?_⟩
  intro j x
  constructor
  · intro member
    exact ⟨i, T, S, E, last, member⟩
  · rintro ⟨k, U, F, G, entry, member⟩
    have extension := mainPrefixExtends_iff.1 (history k _ entry)
    have subset : (Fin.cases U (Fin.cases F (fun _ => G)) : Fin 3 → ZFSet.{u}) j ⊆
        (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j :=
      Fin.cases extension.1 (Fin.cases extension.2.1 (fun _ => extension.2.2)) j
    exact subset member

theorem OrdinalRecursionTrace.mainPrefix_successor_union {B seed g β p q : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) (insert β β) p)
    (last : ZFSet.pair β q ∈ p) : MainPrefixHistoryUnionCode p q := by
  have history : MainPrefixHistoryExtends p q := by
    intro i old entry
    exact trace.mainPrefix_extends entry last (ZFSet.mem_insert_iff.1 (trace.1.pair_source entry))
  exact history.union_code (trace.mainPrefix_values last).2 last

end

namespace PreservedMainPrefixHistoryCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)
include history

theorem exists_unique_groundUnionCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (member : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (nonempty : A ≠ ∅) (whole : p ∈ M.sets)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD) :
    ∃ q ∈ M.sets, MainPrefixHistoryUnionCode p q ∧
      q ∈ level.recursionPrefixes (M.groundOmegaOne pairing unions powers separation collection infinite)
        Labels C D rD ∧
      (∃ S E, q = mainPrefixCode A S E) ∧
      (∀ i old, ZFSet.pair i old ∈ p → MainPrefixExtends old q) ∧
      ∀ r, MainPrefixHistoryUnionCode p r → r = q := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have domain := M.transitive spec.1 member
  have ordinalA := ordinalSetProperty_member spec.2.1 member
  have small : GroundBelow M A K :=
    ⟨ZFSet.omega, conditions.2.1,
      M.groundOmegaOne_member_countable pairing unions powers separation collection infinite member⟩
  have ground := history.unionCode_ground pairing unions powers separation domain whole
  have candidate := history.union_mem_recursionPrefixes pairing unions powers separation collection
    hK conditions.1 conditions.2.2.1
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    domain whole small level candidates member nonempty ordinalA
  refine ⟨history.graphFamily.unionCode, ground, history.union_code, candidate, ?_, ?_, ?_⟩
  · refine ⟨history.graphFamily.stageUnion, history.graphFamily.transitionUnion, ?_⟩
    unfold MainPrefixGraphFamily.unionCode
    rw [history.graphFamily_indexUnion ordinalA]
  · intro i old entry
    let k := SetMembers.ofMem i (history.function.pair_source entry)
    have actual : ZFSet.pair i (history.graphFamily.code k) ∈ p := by
      simpa only [k, SetMembers.raw_ofMem] using history.graphFamily_code_entry k
    have equal := history.function.unique entry actual
    rw [equal]
    exact history.graphFamily.code_extends_union k
  · intro r code
    exact code.unique history.union_code

end PreservedMainPrefixHistoryCode

section
open SetFormula
universe u

def mainPrefixTraceParams (B seed g : ZFSet.{u}) : Fin 3 → ZFSet.{u} :=
  Fin.cases B (Fin.cases seed (fun _ => g))

def mainPrefixRecursionFormula : SetFormula 6 :=
  mainPrefixTraceStepFormula 3 4 5 0 1 2

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixTraceParams_ground {B seed g : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets) :
    ∀ j, mainPrefixTraceParams B seed g j ∈ M.sets :=
  Fin.cases hB (Fin.cases hSeed (fun _ => hg))

theorem realize_mainPrefixRecursionFormula {B seed g α p y : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets)
    (hα : α ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets mainPrefixRecursionFormula
      (extend α (extend p (extend y (mainPrefixTraceParams B seed g)))) ↔
      MainPrefixTraceStepCode B seed g α p y :=
  M.realize_mainPrefixTraceStepFormula 3 4 5 0 1 2 _
    (Fin.cases hα (Fin.cases hp (Fin.cases hy (M.mainPrefixTraceParams_ground hB hSeed hg))))

theorem mainPrefix_codeTrace {B seed g A p : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets) (hA : A ∈ M.sets)
    (trace : OrdinalRecursionTrace
      (groundRecursionStep M mainPrefixRecursionFormula (mainPrefixTraceParams B seed g)) A p) :
    OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p := by
  refine ⟨trace.1, ?_⟩
  intro α member y entry
  have step := trace.2 α member y entry
  exact (M.realize_mainPrefixRecursionFormula hB hSeed hg (M.transitive hA member) step.1 step.2.1).1
    step.2.2

end TransitiveGround

end

section
universe u

theorem MainPrefixTraceStepCode.selected_of_nonzero {B seed g α p y : ZFSet.{u}}
    (step : MainPrefixTraceStepCode B seed g α p y) (nonzero : α ≠ ∅) :
    ∃ input, MainPrefixHistoryUnionCode p input ∧ ZFSet.pair input y ∈ g := by
  rcases step.2.2.2 with ⟨zero, _⟩ | ⟨_, chosen⟩
  · exact False.elim (nonzero zero)
  · exact chosen

namespace OrdinalRecursionTrace
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_zero_entry (zero : (∅ : ZFSet.{u}) ∈ A) : ZFSet.pair ∅ seed ∈ p := by
  obtain ⟨y, entry⟩ := trace.1.total zero
  have step := trace.2 ∅ zero y entry
  rcases step.2.2.2 with ⟨_, equal⟩ | ⟨nonzero, _⟩
  · exact equal ▸ entry
  · exact False.elim (nonzero rfl)

theorem mainPrefix_successor_entry (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    ZFSet.pair old next ∈ g := by
  have ordinalIndex := ordinalSetProperty_member ordinal member
  have subset : insert β β ⊆ A := fun x hx => ordinal.1 _ member x hx
  have earlier := trace.restrict ordinalIndex subset
  have oldRestricted : ZFSet.pair β old ∈ graphRestriction (insert β β) p :=
    pair_mem_graphRestriction.2 ⟨oldEntry, ZFSet.mem_insert _ _⟩
  have unionOld := earlier.mainPrefix_successor_union oldRestricted
  have nonzero : insert β β ≠ ∅ := by
    intro zero
    exact ZFSet.notMem_empty β (zero ▸ ZFSet.mem_insert β β)
  obtain ⟨input, unionInput, entry⟩ :=
    (trace.2 _ member next nextEntry).selected_of_nonzero nonzero
  exact unionInput.unique unionOld ▸ entry

end OrdinalRecursionTrace

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mainPrefixTraceStepClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) {Labels C D rD B seed g : ZFSet.{u}}
    (domain : B = level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD)
    (hB : B ∈ M.sets) (seedMember : seed ∈ B)
    (seedIndex : MainPrefixAtIndex (insert ∅ ∅) seed) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc B B g)
    (advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next) :
    GroundOrdinalStepClosure M
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      mainPrefixRecursionFormula (mainPrefixTraceParams B seed g) := by
  have hSeed := M.transitive hB seedMember
  have hOmega := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have graph : FunctionGraphOn B g := ⟨B, function⟩
  have candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q := by
    intro q member
    rw [domain] at member
    exact (level.mem_preservedMainPrefixes.1 (level.mem_recursionPrefixes.1 member).1).2
  intro α member p hp trace
  have hα := M.transitive hOmega member
  have actual := M.mainPrefix_codeTrace hB hSeed hg hα trace
  have finish : ∀ y ∈ M.sets, MainPrefixTraceStepCode B seed g α p y →
      ∃ y ∈ M.sets, Realize M.sets mainPrefixRecursionFormula
        (extend α (extend p (extend y (mainPrefixTraceParams B seed g)))) ∧
        ∀ z ∈ M.sets, Realize M.sets mainPrefixRecursionFormula
          (extend α (extend p (extend z (mainPrefixTraceParams B seed g)))) → z = y := by
    intro y hy code
    refine ⟨y, hy, (M.realize_mainPrefixRecursionFormula hB hSeed hg hα hp hy).2 code, ?_⟩
    intro z hz recognized
    exact ((M.realize_mainPrefixRecursionFormula hB hSeed hg hα hp hz).1 recognized).unique graph code
  by_cases zero : α = ∅
  · apply finish seed hSeed
    refine ⟨seedMember, zero.symm ▸ seedIndex, ?_, Or.inl ⟨zero, rfl⟩⟩
    intro i old entry
    have impossible := trace.1.pair_source entry
    rw [zero] at impossible
    exact False.elim (ZFSet.notMem_empty i impossible)
  · have history := actual.preservedMainPrefixHistory candidates
    have storedCandidates : ∀ i q, ZFSet.pair i q ∈ p →
        q ∈ level.preservedMainPrefixes Labels C D rD := by
      intro i q entry
      have member := (actual.mainPrefix_values entry).1
      rw [domain] at member
      exact (level.mem_recursionPrefixes.1 member).1
    obtain ⟨input, _, unionCode, inputMember, inputIndex, extension, _⟩ :=
      history.exists_unique_groundUnionCode pairing unions powers separation collection infinite
        hK standard member zero hp level storedCandidates
    have inputB : input ∈ B := domain.symm ▸ inputMember
    obtain ⟨y, entry⟩ := graph.total inputB
    have yB := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    obtain ⟨index, stepExtension⟩ := advance input y α entry inputIndex
    apply finish y (M.transitive hB yB)
    exact ⟨yB, index, fun i old oldEntry => (extension i old oldEntry).trans stepExtension,
      Or.inr ⟨zero, input, unionCode, entry⟩⟩

theorem exists_unique_selectedMainPrefixTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) {Labels C D rD B seed g : ZFSet.{u}}
    (domain : B = level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD)
    (hB : B ∈ M.sets) (seedMember : seed ∈ B)
    (seedIndex : MainPrefixAtIndex (insert ∅ ∅) seed) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc B B g)
    (advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next) :
    ∃ p ∈ M.sets,
      OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
        (M.groundOmegaOne pairing unions powers separation collection infinite) p ∧
      ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
        (M.groundOmegaOne pairing unions powers separation collection infinite) q → q = p := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hSeed := M.transitive hB seedMember
  have closure := M.mainPrefixTraceStepClosure pairing unions powers separation collection infinite
    hK standard level domain hB seedMember seedIndex hg function advance
  obtain ⟨p, hp, trace, _, _⟩ := M.exists_unique_ordinalRecursionTrace pairing unions separation
    collection spec.1 spec.2.1 mainPrefixRecursionFormula (mainPrefixTraceParams B seed g)
    (M.mainPrefixTraceParams_ground hB hSeed hg) closure
  have actual := M.mainPrefix_codeTrace hB hSeed hg spec.1 trace
  refine ⟨p, hp, actual, ?_⟩
  intro q other
  exact other.unique actual spec.2.1 (fun _ hx => hx)
    (fun _ _ _ _ _ _ first second => first.unique ⟨B, function⟩ second)

end TransitiveGround

namespace OrdinalRecursionTrace
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem exists_groundTerminalPrefixCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (ordinal : ordinalSetProperty A) (whole : p ∈ M.sets)
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    ∃ q ∈ M.sets, MainPrefixHistoryUnionCode p q ∧ MainPrefixAtIndex A q ∧
      PreservedMainPrefixCode M K Labels C D rD q ∧ MainPrefixHistoryExtends p q ∧
      ∀ r, MainPrefixHistoryUnionCode p r → r = q := by
  have history := trace.preservedMainPrefixHistory candidates
  let family := history.graphFamily
  have index := history.graphFamily_indexUnion ordinal
  have ground := history.unionCode_ground pairing unions powers separation hA whole
  refine ⟨family.unionCode, ground, history.union_code, ?_, ?_, ?_, ?_⟩
  · refine ⟨family.stageUnion, family.transitionUnion, ?_⟩
    change mainPrefixCode family.indexUnion family.stageUnion family.transitionUnion = _
    rw [index]
  · exact ⟨family.indexUnion, family.stageUnion, family.transitionUnion, rfl,
      family.union_valid, family.union_profile_graph_code history.graphFamily_profiles⟩
  · intro i old entry
    let k := SetMembers.ofMem i (trace.1.pair_source entry)
    have actual : ZFSet.pair i (family.code k) ∈ p := by
      simpa only [k, family, SetMembers.raw_ofMem] using history.graphFamily_code_entry k
    have equal := trace.1.unique entry actual
    rw [equal]
    exact family.code_extends_union k
  · intro r recognized
    exact recognized.unique history.union_code

end OrdinalRecursionTrace

namespace OrdinalRecursionTrace
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem exists_groundTerminalPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (ordinal : ordinalSetProperty A) (whole : p ∈ M.sets)
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    ∃ ordinalA : ordinalSetProperty A,
      letI := ordinalMainIndexPreorder ordinalA
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers A),
        run.indices = A ∧ run.PreservesOldProfiles ∧ MainPrefixHistoryUnionCode p run.code ∧
        MainPrefixHistoryExtends p run.code ∧
        ∀ q, MainPrefixHistoryUnionCode p q → q = run.code := by
  obtain ⟨q, hq, union, index, preserved, extension, unique⟩ :=
    trace.exists_groundTerminalPrefixCode pairing unions powers separation hA ordinal whole candidates
  obtain ⟨T, _, ordinalT, run, indices, equal, profiles⟩ :=
    preserved.exists_decodedPrefix pairing unions powers separation hq
  let := ordinalMainIndexPreorder ordinalT
  have indexT : MainPrefixAtIndex T q := by
    refine ⟨run.stageGraph, run.transitionGraph, ?_⟩
    rw [← equal]
    change mainPrefixCode run.indices _ _ = _
    rw [indices]
  have same := indexT.unique index
  subst T
  refine ⟨ordinalT, run, indices, profiles, ?_, ?_, ?_⟩
  · exact equal.symm ▸ union
  · exact equal.symm ▸ extension
  · intro r recognized
    exact (unique r recognized).trans equal.symm

end OrdinalRecursionTrace

namespace OrdinalRecursionTrace
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p q : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem terminalCode_ranked_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K)) (hA : A ∈ M.sets) (whole : p ∈ M.sets)
    (small : GroundBelow M A K) (level : GroundMainCandidateLevel M K)
    (candidates : ∀ z ∈ B, z ∈ level.preservedMainPrefixes Labels C D rD)
    (terminal : MainPrefixHistoryUnionCode p q) :
    q ∈ M.sets ∧ ZFSet.rank q < ZFSet.rank K ∧
      q ∈ level.preservedMainPrefixes Labels C D rD := by
  have preserved : ∀ z ∈ B, PreservedMainPrefixCode M K Labels C D rD z := by
    intro z member
    exact (level.mem_preservedMainPrefixes.1 (candidates z member)).2
  have history := trace.preservedMainPrefixHistory preserved
  have ranked := history.ranked_union_candidate pairing unions powers separation collection
    hK ordinalK regular limit hA whole small level
    (fun _ z entry => candidates z (trace.mainPrefix_values entry).1)
  exact (terminal.unique history.union_code).symm ▸ ranked

theorem groundOmegaOne_terminalCode_ranked_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (domain : A = M.groundOmegaOne pairing unions powers separation collection infinite)
    (whole : p ∈ M.sets) (level : GroundMainCandidateLevel M K)
    (candidateDomain : B = level.recursionPrefixes A Labels C D rD)
    (terminal : MainPrefixHistoryUnionCode p q) :
    GroundBelow M A K ∧ q ∈ M.sets ∧ ZFSet.rank q < ZFSet.rank K ∧
      q ∈ level.preservedMainPrefixes Labels C D rD := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have hA : A ∈ M.sets := domain.symm ▸
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have member : A ∈ K := domain.symm ▸
    standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK
  have small := GroundBelow.of_member pairing unions powers separation hK member
  refine ⟨small, trace.terminalCode_ranked_candidate pairing unions powers separation collection
    hK conditions.1 conditions.2.2.1 (conditions.rank_isLimit pairing unions powers separation infinite hK)
    hA whole small level ?_ terminal⟩
  intro z hz
  rw [candidateDomain] at hz
  exact (level.mem_recursionPrefixes.1 hz).1

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
