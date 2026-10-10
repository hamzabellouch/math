import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageThreeInternalClosure

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def StageOneConditionCode (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (z : ZFSet.{u}) : Prop :=
  ∃ p A, z = ZFSet.pair p A ∧ stageOneRawTests M d A (ZFSet.pair p ∅)

namespace SetFormula

def stageOneConditionFormula {n : Nat} (d : Fin 15 → Fin n) (z : Fin n) : SetFormula n :=
  let old := suffixIndex n 4
  let v := prefixIndex n 4
  exBlock 4 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (.conj (BoundedFormula.emptyFormula (v 2)).toFormula
      (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 2)).toFormula
        (stageOneTestsFormula (fun j => old (d j)) (v 1) (v 3)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (d : Fin 15 → Fin n) (z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneConditionFormula d z) env ↔
      StageOneConditionCode M (fun j => env (d j)) (env z) := by
  rw [stageOneConditionFormula, realize_exBlock]
  have actual (f : Fin 4 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 4 z) (prefixIndex n 4 0) (prefixIndex n 4 1)).toFormula
        (.conj (BoundedFormula.emptyFormula (prefixIndex n 4 2)).toFormula
          (.conj (BoundedFormula.orderedPairFormula (prefixIndex n 4 3) (prefixIndex n 4 0) (prefixIndex n 4 2)).toFormula
            (stageOneTestsFormula (fun j => suffixIndex n 4 (d j)) (prefixIndex n 4 1) (prefixIndex n 4 3)))))
          (extendMany 4 f env) ↔
        env z = ZFSet.pair (f 0) (f 1) ∧ f 2 = ∅ ∧ f 3 = ZFSet.pair (f 0) (f 2) ∧
          stageOneRawTests M (fun j => env (d j)) (f 1) (f 3) := by
    have allground := extendMany_members 4 f env ground members
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground, BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix, extendMany_suffix]
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground, BoundedFormula.truth_emptyFormula]
      simp only [extendMany_prefix]
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground, BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix]
    rw [M.realize_stageOneTestsFormula _ _ _ _ allground]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨pair, empty, lower, tests⟩ := (actual f ground).1 body
    refine ⟨f 0, f 1, pair, ?_⟩
    rw [empty] at lower
    exact lower ▸ tests
  · rintro ⟨p, A, equal, tests⟩
    have hp : p ∈ M.sets := M.pair_left (equal ▸ members z)
    have hA : A ∈ M.sets := M.pair_right (equal ▸ members z)
    have empty : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨env z, members z⟩
    have lower := M.orderedPair_mem pairing hp empty
    let f : Fin 4 → ZFSet.{u} := ![p,A,∅,ZFSet.pair p ∅]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases hp (Fin.cases hA (Fin.cases empty (Fin.cases lower (fun j => Fin.elim0 j))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal,rfl,rfl,tests⟩⟩

noncomputable def stageOneConditions (rawRowCarrier : ZFSet.{u}) (d : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (StageOneConditionCode M d) (M.stageOneCandidateBound rawRowCarrier (d 0) (d 6))

theorem mem_stageOneConditions (rawRowCarrier : ZFSet.{u}) (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ M.stageOneConditions rawRowCarrier d ↔
      z ∈ M.stageOneCandidateBound rawRowCarrier (d 0) (d 6) ∧ StageOneConditionCode M d z :=
  ZFSet.mem_sep

theorem pair_mem_stageOneConditions (rawRowCarrier : ZFSet.{u}) (d : Fin 15 → ZFSet.{u}) (p A : ZFSet.{u}) :
    ZFSet.pair p A ∈ M.stageOneConditions rawRowCarrier d ↔
      p ∈ rawRowCarrier ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments (d 0) (d 6) ∧
        M.groundEmbeddable A ZFSet.omega ∧ stageOneRawTests M d A (ZFSet.pair p ∅) := by
  rw [M.mem_stageOneConditions, M.pair_mem_stageOneCandidateBound]
  constructor
  · rintro ⟨⟨hp,hA,subset,small⟩,p',A',equal,tests⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hp,hA,subset,small,tests⟩
  · rintro ⟨hp,hA,subset,small,tests⟩
    exact ⟨⟨hp,hA,subset,small⟩,p,A,rfl,tests⟩

theorem stageOneConditions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rawRowCarrier : ZFSet.{u}} (d : Fin 15 → ZFSet.{u}) (hRow : rawRowCarrier ∈ M.sets)
    (members : ∀ j, d j ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneConditions rawRowCarrier d ∈ M.sets := by
  have bound := M.stageOneCandidateBound_mem pairing unions powers separation hRow (members 0) (members 6) omega
  let phi : SetFormula 16 := stageOneConditionFormula Fin.succ 0
  have ground := M.separation_mem separation phi d members bound
  have equal : ZFSet.sep (fun z => Realize M.sets phi (extend z d))
      (M.stageOneCandidateBound rawRowCarrier (d 0) (d 6)) = M.stageOneConditions rawRowCarrier d := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_stageOneConditions]
    apply and_congr_right
    intro hz
    exact M.realize_stageOneConditionFormula pairing Fin.succ 0 (extend z d)
      (Fin.cases (M.transitive bound hz) members)
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid) (T2 : ZFSet.{u})

structure StageOneCondition where
  row : P
  assignments : ZFSet.{u}
  assignments_mem : assignments ∈ M.groundSmallSubsets
    (stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) ZFSet.omega
  tests : M.stageOneTests s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 assignments row

namespace StageOneCondition
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

@[ext] theorem ext {p q : Condition} (rows : p.row = q.row) (data : p.assignments = q.assignments) : p = q := by
  cases p
  cases q
  cases rows
  cases data
  rfl

noncomputable def empty (row : P) : Condition where
  row := row
  assignments := ∅
  assignments_mem := (M.mem_groundSmallSubsets _ _ ∅).2
    ⟨M.empty_mem ⟨T, hT⟩, ZFSet.empty_subset _, M.empty_groundEmbeddable ZFSet.omega ⟨T, hT⟩⟩
  tests := M.stageOneTests_empty s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 row

theorem empty_row (row : P) :
    (empty M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2 row).row = row := rfl

theorem empty_assignments (row : P) :
    (empty M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2 row).assignments = ∅ := rfl

end StageOneCondition





namespace StageOneCondition
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

instance partialOrder : PartialOrder Condition where
  le p q := p.row ≤ q.row ∧ q.assignments ⊆ p.assignments
  le_refl _ := ⟨le_rfl, fun _ h => h⟩
  le_trans _ _ _ first second := ⟨first.1.trans second.1, fun _ h => first.2 (second.2 h)⟩
  le_antisymm p q first second := by
    apply ext M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2
      (le_antisymm first.1 second.1)
    apply ZFSet.ext
    intro z
    exact ⟨fun h => second.2 h, fun h => first.2 h⟩

theorem le_iff (p q : Condition) : p ≤ q ↔ p.row ≤ q.row ∧ q.assignments ⊆ p.assignments := Iff.rfl

def rowProjection : Condition →o P where
  toFun p := p.row
  monotone' _ _ below := below.1

noncomputable def emptyEmbedding : P ↪o Condition where
  toFun := empty M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2
  inj' _ _ equal := congrArg StageOneCondition.row equal
  map_rel_iff' := ⟨fun below => below.1, fun below => ⟨below, fun _ h => h⟩⟩

noncomputable instance orderTop : OrderTop Condition where
  top := empty M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2 ⊤
  le_top p := ⟨le_top, ZFSet.empty_subset p.assignments⟩

theorem rowProjection_empty (row : P) :
    rowProjection M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2
      (empty M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2 row) = row := rfl

end StageOneCondition




namespace StageOneCondition
variable {M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2}
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

noncomputable def withRow (p : Condition) (row : P) (below : row ≤ p.row) : Condition where
  row := row
  assignments := p.assignments
  assignments_mem := p.assignments_mem
  tests := M.stageOneTests_mono s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 p.assignments p.tests below

theorem withRow_row (p : Condition) (row : P) (below : row ≤ p.row) :
    (p.withRow row below).row = row := rfl

theorem withRow_assignments (p : Condition) (row : P) (below : row ≤ p.row) :
    (p.withRow row below).assignments = p.assignments := rfl

theorem withRow_le (p : Condition) (row : P) (below : row ≤ p.row) :
    p.withRow row below ≤ p := ⟨below, fun _ h => h⟩

theorem exists_lift_row (p : Condition) (row : P) (below : row ≤ p.row) :
    ∃ q : Condition, q ≤ p ∧ q.row = row ∧ q.assignments = p.assignments :=
  ⟨p.withRow row below, p.withRow_le row below, rfl, rfl⟩

end StageOneCondition




namespace StageOneCondition
variable {M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2}
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

noncomputable def code (p : Condition) (c : Presentation P) : ZFSet.{u} :=
  ZFSet.pair (c.encode p.row) p.assignments

theorem code_eq_iff (c : Presentation P) (p q : Condition) :
    p.code c = q.code c ↔ p.row = q.row ∧ p.assignments = q.assignments := by
  rw [code, code, ZFSet.pair_inj]
  exact and_congr c.injective.eq_iff Iff.rfl

theorem code_injective (c : Presentation P) : Function.Injective (fun p : Condition => p.code c) := by
  intro p q equal
  obtain ⟨rows, assignments⟩ := (code_eq_iff c p q).1 equal
  exact ext M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2 rows assignments

theorem code_mem_candidateBound (c : Presentation P) (p : Condition) :
    p.code c ∈ M.stageOneCandidateBound c.carrier
      (M.niceRefinementIndices a s b d ∅ T T2 valid) T :=
  ZFSet.pair_mem_prod.2 ⟨c.encode_mem p.row, p.assignments_mem⟩

instance small : Small.{u} Condition := by
  let bound := M.stageOneCandidateBound s.carrier (M.niceRefinementIndices a s b d ∅ T T2 valid) T
  let f : Condition → bound := fun p => ⟨p.code s, code_mem_candidateBound s p⟩
  apply small_of_injective.{u} (f := f)
  intro p q equal
  exact code_injective s (congrArg Subtype.val equal)

end StageOneCondition




namespace StageOneCondition
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

noncomputable def chainUnion (seq : Nat → Condition) (decreasing : Antitone seq) (row : P)
    (below : ∀ n, row ≤ (seq n).row)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ M.groundSmallSubsets
      (stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) ZFSet.omega) : Condition where
  row := row
  assignments := stageOneAssignmentUnion (fun n => (seq n).assignments)
  assignments_mem := small
  tests := M.stageOneTests_union s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 (fun n => (seq n).assignments) (fun n => (seq n).row) row
    (fun _ _ less => (decreasing less).2) below (fun n => (seq n).tests)

theorem chainUnion_row (seq : Nat → Condition) (decreasing : Antitone seq) (row : P)
    (below : ∀ n, row ≤ (seq n).row)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ M.groundSmallSubsets
      (stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) ZFSet.omega) :
    (chainUnion M s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 seq decreasing row below small).row = row := rfl

theorem chainUnion_assignments (seq : Nat → Condition) (decreasing : Antitone seq) (row : P)
    (below : ∀ n, row ≤ (seq n).row)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ M.groundSmallSubsets
      (stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) ZFSet.omega) :
    (chainUnion M s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 seq decreasing row below small).assignments =
        stageOneAssignmentUnion (fun n => (seq n).assignments) := rfl

theorem chainUnion_le (seq : Nat → Condition) (decreasing : Antitone seq) (row : P)
    (below : ∀ n, row ≤ (seq n).row)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ M.groundSmallSubsets
      (stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) ZFSet.omega) (n : Nat) :
    chainUnion M s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 seq decreasing row below small ≤ seq n :=
  ⟨below n, stageOneAssignmentUnion_contains (fun n => (seq n).assignments) n⟩

end StageOneCondition
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)

noncomputable def stageOneForcing : ZFSet.{u} :=
  M.stageOneConditions c.carrier (M.stageOneFormulaData a c.pairEmpty b d T T2 valid)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)

include pairing unions powers separation carrier order nodes hT indices system in
theorem stageOneForcing_mem (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneForcing a c b d T T2 valid ∈ M.sets := by
  have pairedCarrier := M.pairEmpty_carrier_mem pairing unions powers separation c carrier
  have pairedOrder := M.pairEmpty_order_mem pairing unions powers separation c carrier order
  exact M.stageOneConditions_mem pairing unions powers separation _ carrier
    (M.stageOneFormulaData_members a c.pairEmpty b d T T2 valid pairing unions powers separation
      hT pairedCarrier pairedOrder nodes nodeOrder valid2 indices base directed system) omega

variable (collection : CollectionSchema M.sets)

include nodes indices in
theorem stageOneForcing_entry (p : P) (A : ZFSet.{u}) :
    ZFSet.pair (c.encode p) A ∈ M.stageOneForcing a c b d T T2 valid ↔
      A ∈ M.groundSmallSubsets
        (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) ZFSet.omega ∧
      M.stageOneTests c.pairEmpty pairing unions powers separation collection
        (M.pairEmpty_carrier_mem pairing unions powers separation c carrier)
        (M.pairEmpty_order_mem pairing unions powers separation c carrier order) hT valid
        a b d base directed system T2 A p := by
  rw [stageOneForcing, M.pair_mem_stageOneConditions, M.mem_groundSmallSubsets]
  have tests := M.stageOneRawTests_iff a c.pairEmpty b d pairing unions powers separation collection
    (M.pairEmpty_carrier_mem pairing unions powers separation c carrier)
    (M.pairEmpty_order_mem pairing unions powers separation c carrier order) nodes hT valid indices
    base directed system A p
  constructor
  · rintro ⟨_, ground, subset, small, raw⟩
    exact ⟨⟨ground, subset, small⟩, tests.1 raw⟩
  · rintro ⟨⟨ground, subset, small⟩, typed⟩
    exact ⟨c.encode_mem p, ground, subset, small, tests.2 typed⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "Q" => M.stageOneForcing a c b d T T2 valid

include nodes indices in
theorem stageOneConditionCode_mem (p : Condition) : p.code c ∈ Q :=
  (M.stageOneForcing_entry a c b d T T2 valid pairing unions powers separation carrier order nodes hT
    indices base directed system collection p.row p.assignments).2 ⟨p.assignments_mem, p.tests⟩

include nodes indices in
theorem exists_stageOneConditionCode {z : ZFSet.{u}} (member : z ∈ Q) :
    ∃ p : Condition, p.code c = z := by
  have candidate := (M.mem_stageOneConditions c.carrier
    (M.stageOneFormulaData a c.pairEmpty b d T T2 valid) z).1 member
  obtain ⟨row, A, small, equal⟩ := M.exists_stageOneCandidate_fields c _ _ candidate.1
  have tests := (M.stageOneForcing_entry a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection row A).1 (equal ▸ member)
  exact ⟨⟨row, A, small, tests.2⟩, equal.symm⟩

include nodes indices in
theorem stageOneConditionCode_range :
    ZFSet.range (fun p : Condition => p.code c) = Q := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact M.stageOneConditionCode_mem a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection p
  · intro member
    exact M.exists_stageOneConditionCode a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection member

noncomputable def stageOneConditionEquiv : Condition ≃ SetMembers Q :=
  Equiv.ofBijective
    (fun p => SetMembers.ofMem (p.code c) (M.stageOneConditionCode_mem a c b d T T2 valid
      pairing unions powers separation carrier order nodes hT indices base directed system collection p))
    ⟨by
      intro p q equal
      apply StageOneCondition.code_injective c
      have raw := congrArg SetMembers.raw equal
      simpa only [SetMembers.raw_ofMem] using raw,
     by
      intro x
      obtain ⟨p, equal⟩ := M.exists_stageOneConditionCode a c b d T T2 valid
        pairing unions powers separation carrier order nodes hT indices base directed system collection
        (SetMembers.raw_mem x)
      refine ⟨p, SetMembers.raw_injective Q ?_⟩
      exact (SetMembers.raw_ofMem _ _).trans equal⟩

theorem stageOneConditionEquiv_raw (p : Condition) :
    SetMembers.raw (M.stageOneConditionEquiv a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection p) = p.code c :=
  SetMembers.raw_ofMem _ _

noncomputable def stageOneConditionPresentation : Presentation (Shrink Condition) where
  carrier := Q
  encode x := ((equivShrink Condition).symm x).code c
  injective := StageOneCondition.code_injective c |>.comp (equivShrink Condition).symm.injective
  mem_carrier z := by
    constructor
    · intro member
      obtain ⟨p, equal⟩ := M.exists_stageOneConditionCode a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection member
      exact ⟨equivShrink Condition p, by simpa only [Equiv.symm_apply_apply] using equal⟩
    · rintro ⟨x, equal⟩
      exact equal ▸ M.stageOneConditionCode_mem a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection ((equivShrink Condition).symm x)

theorem stageOneConditionPresentation_encode (p : Condition) :
    (M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection).encode (equivShrink Condition p) = p.code c := by
  exact congrArg (fun q : Condition => q.code c) ((equivShrink Condition).symm_apply_apply p)

include nodes indices system in
theorem stageOneConditionPresentation_carrier_mem
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    (M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection).carrier ∈ M.sets :=
  M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation carrier order nodes hT
    indices base directed system nodeOrder omega

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "Q" => M.stageOneForcing a c b d T T2 valid

local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "emptyRow" => StageOneCondition.empty M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2

noncomputable def stageOneEmptyInclusion (p : P) : Shrink Condition :=
  equivShrink Condition (emptyRow p)

local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection

theorem stageOneEmptyInclusion_encode (p : P) :
    (pres).encode (incl p) = c.pairEmpty.encode p :=
  M.stageOneConditionPresentation_encode a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection (emptyRow p)

theorem stageOneEmptyInclusion_lowerGraph :
    c.pairEmpty.graph (pres) incl = identityFunctionGraph c.pairEmpty.carrier := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨p, rfl⟩
    rw [M.stageOneEmptyInclusion_encode a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection p]
    exact ⟨c.pairEmpty.encode p, c.pairEmpty.encode_mem p, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := (c.pairEmpty.mem_carrier x).1 hx
    exact ⟨p, congrArg (ZFSet.pair (c.pairEmpty.encode p))
      (M.stageOneEmptyInclusion_encode a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection p)⟩

theorem stageOneEmptyInclusion_lowerGraph_mem :
    c.pairEmpty.graph (pres) incl ∈ M.sets := by
  rw [M.stageOneEmptyInclusion_lowerGraph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection]
  exact M.identityFunctionGraph_mem pairing unions powers separation pairedCarrier

theorem stageOneEmptyInclusion_originalGraph :
    c.graph (pres) incl = c.graph c.pairEmpty id := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, Presentation.mem_graph]
  simp only [M.stageOneEmptyInclusion_encode a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection, id_eq]

theorem stageOneEmptyInclusion_originalGraph_mem : c.graph (pres) incl ∈ M.sets := by
  rw [M.stageOneEmptyInclusion_originalGraph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection]
  exact M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier

noncomputable def stageOneNameLift (tau : Name c.pairEmpty) : Name (pres) :=
  Name.rename (pres) incl tau

theorem stageOneNameLift_val (tau : Name c.pairEmpty) :
    (M.stageOneNameLift a c b d T T2 valid pairing unions powers separation carrier order nodes hT
      indices base directed system collection tau).val = tau.val :=
  Name.rename_val_of_encode (pres) incl
    (M.stageOneEmptyInclusion_encode a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection) tau

theorem stageOneNameLift_mem (tau : Name c.pairEmpty) (ground : tau.val ∈ M.sets) :
    (M.stageOneNameLift a c b d T T2 valid pairing unions powers separation carrier order nodes hT
      indices base directed system collection tau).val ∈ M.sets := by
  rw [M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation carrier order nodes hT
    indices base directed system collection]
  exact ground

theorem stageOneNameLift_eval (H : Set (Shrink Condition)) (tau : Name c.pairEmpty) :
    Name.eval H (M.stageOneNameLift a c b d T T2 valid pairing unions powers separation carrier order nodes hT
      indices base directed system collection tau) = Name.eval {p | incl p ∈ H} tau :=
  Name.eval_rename (pres) incl H tau

end PartitionPilot.Forcing.TransitiveGround

end OAI
