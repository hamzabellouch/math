import OAI.SetTheory.PartitionPrinciple.Forcing.FlatSuccessorConditionUnions

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem exists_stageOneAssignment_fields
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    {T T2 : ZFSet.{u}} {valid : ∀ z ∈ T, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (system : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)
    (hT : T ∈ M.sets) {z : ZFSet.{u}}
    (member : z ∈ stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T) :
    ∃ C E : L, ∃ U Rf Rc u w : (M.nameDomain s).names,
      refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d ∅ T T2 valid ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      z = stageOneAssignment
        (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val := by
  obtain ⟨t, ht, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments _ T z).1 member
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ := system.decoded t ht
  let u : (M.nameDomain s).names := ⟨⟨rawU, valid rawU hu⟩, M.transitive hT hu⟩
  let w : (M.nameDomain s).names := ⟨⟨rawW, valid rawW hw⟩, M.transitive hT hw⟩
  exact ⟨C, E, U, Rf, Rc, u, w, ht, hu, hw, rfl⟩

omit [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L] in
theorem exists_stageOneCandidate_fields (c : Presentation P) (I T : ZFSet.{u})
    {z : ZFSet.{u}} (member : z ∈ M.stageOneCandidateBound c.carrier I T) :
    ∃ p : P, ∃ A ∈ M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega,
      z = ZFSet.pair (c.encode p) A := by
  obtain ⟨raw, hp, A, hA, equal⟩ := ZFSet.mem_prod.1 member
  obtain ⟨p, rfl⟩ := (c.mem_carrier raw).1 hp
  exact ⟨p, A, hA, equal⟩

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (rawRowCarrier I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T

include nodes indices in
theorem stageThreeForcing_entry (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.stageThreeForcing rawRowCarrier I0 I1 a s b d T T2 valid ↔
      row ∈ rawRowCarrier ∧
      A ∈ M.groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega ∧
      ∃ lower : P, s.encode lower = ZFSet.pair row (assignmentCut levels (natSetCode 2) A) ∧
        M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
          a b d base directed system (natSetCode 2) T2 A lower := by
  rw [M.stageThreeForcing_raw_entry]
  constructor
  · rintro ⟨rowMem, small, lowerMem, raw⟩
    obtain ⟨lower, equal⟩ := (s.mem_carrier _).1 lowerMem
    refine ⟨rowMem, small, lower, equal, ?_⟩
    apply (M.refinementLevelRawTests_iff a s b d (natSetCode 2)
      pairing unions powers separation collection carrier order nodes hT valid indices
      base directed system A lower).1
    exact equal.symm ▸ raw
  · rintro ⟨rowMem, small, lower, equal, tests⟩
    refine ⟨rowMem, small, equal ▸ s.encode_mem lower, ?_⟩
    have raw := (M.refinementLevelRawTests_iff a s b d (natSetCode 2)
      pairing unions powers separation collection carrier order nodes hT valid indices
      base directed system A lower).2 tests
    exact equal ▸ raw

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
local notation "tests" => M.refinementLevelTests s pairing unions powers separation collection
  carrier order hT valid a b d base directed system (natSetCode 2) T2
local notation "Condition" => FlatSuccessorCondition M c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
local notation "pres" => M.flatSuccessorPresentation c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

include nodes indices in
theorem stageThreeFlatCarrier_eq :
    M.flatSuccessorCarrier c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests =
      M.stageThreeForcing c.carrier I0 I1 a s b d T T2 valid := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨p, rfl⟩ := (M.mem_flatSuccessorCarrier c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests z).1 member
    exact (M.stageThreeForcing_entry c.carrier I0 I1 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system (c.encode p.row) p.assignments).2
      ⟨c.encode_mem p.row, p.assignments_mem, p.lower, p.lower_code, p.tests⟩
  · intro member
    have candidate := (M.mem_stageTwoConditions c.carrier ((I0 ∪ I1) ∪ I2) levels
      (natSetCode 2) (M.refinementLevelFormulaData a s b d (natSetCode 2) T T2 valid) z).1 member
    obtain ⟨row, A, small, equal⟩ := M.exists_stageOneCandidate_fields c _ _ candidate.1
    obtain ⟨_, _, lower, lowerCode, checked⟩ :=
      (M.stageThreeForcing_entry c.carrier I0 I1 a s b d T T2 valid pairing unions powers separation
        collection carrier order nodes hT indices base directed system (c.encode row) A).1 (equal ▸ member)
    exact (M.mem_flatSuccessorCarrier c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests z).2
      ⟨⟨row, A, small, lower, lowerCode, checked⟩, equal.symm⟩

include nodes indices in
theorem stageThreeFlatPresentation_carrier :
    (pres).carrier = M.stageThreeForcing c.carrier I0 I1 a s b d T T2 valid :=
  M.stageThreeFlatCarrier_eq c I0 I1 a s b d T T2 valid pairing unions powers separation collection
    carrier order nodes hT indices base directed system

include nodes indices in
theorem stageThreeFlatPresentation_carrier_mem
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    (pres).carrier ∈ M.sets := by
  rw [M.stageThreeFlatPresentation_carrier c I0 I1 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system]
  exact M.stageThreeForcing_mem c.carrier I0 I1 a s b d T T2 valid pairing unions powers separation
    rows hI0 hI1 hT carrier order nodes nodeOrder valid2 indices base directed system omega

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
local notation "tests" => M.refinementLevelTests s pairing unions powers separation collection
  carrier order hT valid a b d base directed system (natSetCode 2) T2
local notation "Condition" => FlatSuccessorCondition M c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
local notation "pres" => M.flatSuccessorPresentation c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

local notation "smallOrder" => M.flatSuccessorSmallOrder c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

theorem stageThreeFlatOrder_eq :
    letI := smallOrder
    (pres).conditionOrder = rowAssignmentOrder (pres).carrier c.carrier
      (M.groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) ZFSet.omega)
      c.conditionOrder :=
  M.flatSuccessorConditionOrder_eq c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

include nodes indices in
theorem stageThreeFlatOrder_mem
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (rowOrder : c.conditionOrder ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    (pres).conditionOrder ∈ M.sets := by
  let := smallOrder
  have actual := M.stageThreeFlatPresentation_carrier_mem c I0 I1 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    rows hI0 hI1 nodeOrder omega
  exact M.flatSuccessorConditionOrder_mem c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
    pairing unions powers separation rows actual
    (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1)
      indices.index_ground) hT omega rowOrder

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
local notation "tests" => M.refinementLevelTests s pairing unions powers separation collection
  carrier order hT valid a b d base directed system (natSetCode 2) T2
local notation "Condition" => FlatSuccessorCondition M c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
local notation "pres" => M.flatSuccessorPresentation c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
variable (F : FlatConditionSystem M c s (stageOneAssignments (I0 ∪ I1) T))
local notation "restrict" => M.flatSuccessorSmallRestriction c s ((I0 ∪ I1) ∪ I2) T levels
  (natSetCode 2) tests F

include nodes indices in
theorem stageThreeSmallRestriction_graph :
    letI := smallOrder
    (pres).graph s restrict = rowAssignmentCutGraph
      (M.stageThreeForcing c.carrier I0 I1 a s b d T T2 valid) s.carrier levels (natSetCode 2) := by
  let := smallOrder
  rw [← M.stageThreeFlatPresentation_carrier c I0 I1 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system]
  exact (pres).graph_eq_rowAssignmentCutGraph s restrict
    (fun p => c.encode ((equivShrink Condition).symm p).row)
    (fun p => ((equivShrink Condition).symm p).assignments) levels (natSetCode 2)
    (fun _ => rfl)
    (M.flatSuccessorSmallRestriction_encode c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F)

include nodes indices in
theorem stageThreeSmallRestriction_graph_mem
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    (pres).graph s restrict ∈ M.sets := by
  let := smallOrder
  exact M.presentedRowAssignmentCutGraph_mem pairing unions powers separation
    pres s restrict (fun p => c.encode ((equivShrink Condition).symm p).row)
    (fun p => ((equivShrink Condition).symm p).assignments) levels (natSetCode 2)
    (fun _ => rfl)
    (M.flatSuccessorSmallRestriction_encode c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F)
    (M.stageThreeFlatPresentation_carrier_mem c I0 I1 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      rows hI0 hI1 nodeOrder omega)
    carrier (M.stageThreeAssignmentLevels_mem pairing unions powers separation hI0 hI1 indices.index_ground hT)
    (M.transitive omega (natSetCode_mem_omega 2))

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "B" => M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "data" => M.flatSuccessorConditionData c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
variable (unionLaws : FlatSuccessorUnionLaws tests)
local notation "restrict" => M.flatSuccessorSmallRestriction c s I T levels alpha tests F
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (rows : c.carrier ∈ M.sets) (conditions : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets) (lower : s.carrier ∈ M.sets)
variable (hJ : stageOneAssignments I T ∈ M.sets)
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
variable (closed : InternallyCountablyClosed M s)

include F laws unionLaws pairing unions powers separation infinite choice rows conditions lower hJ
  hLevels hAlpha closed in
theorem flatSuccessor_lower_bound :
    letI := smallOrder
    ∀ seq : Nat → Shrink Condition,
      natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets → Antitone seq →
      ∃ q : P, (∀ n, q ≤ restrict (seq n)) ∧ ∃ p : Shrink Condition,
        ((equivShrink Condition).symm p).lower = q ∧
        ((equivShrink Condition).symm p).assignments =
          assignmentSplice levels alpha (F.assignments q)
            (stageOneAssignmentUnion (fun n => ((equivShrink Condition).symm (seq n)).assignments)) ∧
        ∀ n, p ≤ seq n := by
  let := smallOrder
  intro seq whole decreasing
  let typed : Nat → Condition := fun n => (equivShrink Condition).symm (seq n)
  have typedDecreasing : Antitone typed := fun _ _ less => decreasing less
  have lowerDecreasing : Antitone (fun n => restrict (seq n)) :=
    fun _ _ less => (restrict).monotone (decreasing less)
  obtain ⟨lowerGround, dataGround⟩ := M.flatSuccessorSequence_projections_ground
    c s I T levels alpha tests F pairing unions powers separation rows conditions lower hJ
    hLevels hAlpha (M.omega_mem separation infinite) seq whole
  obtain ⟨q, below⟩ := closed (fun n => restrict (seq n)) lowerGround lowerDecreasing
  have smallRaw := M.groundSmallSubset_union_mem pairing unions powers separation infinite choice
    hJ (fun n => data (seq n)) dataGround
  have small : stageOneAssignmentUnion (fun n => (typed n).assignments) ∈ B := by
    simpa only [M.flatSuccessorConditionData_raw] using smallRaw
  let bound : Condition := FlatSuccessorCondition.chainUnion M c s I T levels alpha tests
    F laws unionLaws pairing unions powers separation infinite choice hLevels hAlpha
    typed typedDecreasing q below small
  refine ⟨q, below, equivShrink Condition bound, ?_, ?_, ?_⟩
  · rw [Equiv.symm_apply_apply]
    rfl
  · rw [Equiv.symm_apply_apply]
    rfl
  · intro n
    change (equivShrink Condition).symm (equivShrink Condition bound) ≤ typed n
    rw [Equiv.symm_apply_apply]
    exact FlatSuccessorCondition.chainUnion_le M c s I T levels alpha tests
      F laws unionLaws pairing unions powers separation infinite choice hLevels hAlpha
      typed typedDecreasing q below small n

include F laws unionLaws pairing unions powers separation infinite choice rows conditions lower hJ
  hLevels hAlpha closed in
theorem flatSuccessor_internally_closed :
    letI := smallOrder
    InternallyCountablyClosed M (pres) := by
  let := smallOrder
  intro seq whole decreasing
  obtain ⟨_, _, q, _, _, below⟩ := M.flatSuccessor_lower_bound c s I T levels alpha tests
    F laws unionLaws pairing unions powers separation infinite choice rows conditions lower hJ
    hLevels hAlpha closed seq whole decreasing
  exact ⟨q, below⟩

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 I1 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 2) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I2" => M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
local notation "tests" => M.refinementLevelTests s pairing unions powers separation collection
  carrier order hT valid a b d base directed system (natSetCode 2) T2
local notation "Condition" => FlatSuccessorCondition M c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
local notation "pres" => M.flatSuccessorPresentation c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

local notation "smallOrder" => M.flatSuccessorSmallOrder c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests

variable (F : FlatConditionSystem M c s (stageOneAssignments (I0 ∪ I1) T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
local notation "laws" => M.stageThreeFlatSuccessorLaws s pairing unions powers separation collection
  carrier order hT valid a b d base directed system first second indices.levelCode
local notation "unionLaws" => M.refinementLevelFlatSuccessorUnionLaws s pairing unions powers separation collection
  carrier order hT valid a b d base directed system (natSetCode 2) T2
local notation "restrict" => M.flatSuccessorSmallRestriction c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets)
variable (closed : InternallyCountablyClosed M s)
include nodes indices F first second infinite choice rows hI0 hI1 nodeOrder closed

theorem stageThreeCondition_lower_bound :
    letI := smallOrder
    ∀ seq : Nat → Shrink Condition,
      natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets → Antitone seq →
      ∃ q : P, (∀ n, q ≤ restrict (seq n)) ∧ ∃ p : Shrink Condition,
        ((equivShrink Condition).symm p).lower = q ∧
        ((equivShrink Condition).symm p).assignments =
          assignmentSplice levels (natSetCode 2) (F.assignments q)
            (stageOneAssignmentUnion (fun n => ((equivShrink Condition).symm (seq n)).assignments)) ∧
        ∀ n, p ≤ seq n := by
  let := smallOrder
  exact M.flatSuccessor_lower_bound c s ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F laws unionLaws
    pairing unions powers separation infinite choice rows
    (M.stageThreeFlatPresentation_carrier_mem c I0 I1 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      rows hI0 hI1 nodeOrder (M.omega_mem separation infinite))
    carrier
    (M.stageOneAssignments_mem pairing unions powers separation
      (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) indices.index_ground) hT)
    (M.stageThreeAssignmentLevels_mem pairing unions powers separation hI0 hI1 indices.index_ground hT)
    (M.transitive (M.omega_mem separation infinite) (natSetCode_mem_omega 2)) closed

theorem stageThreeCondition_internally_closed :
    letI := smallOrder
    InternallyCountablyClosed M (pres) := by
  let := smallOrder
  intro seq whole decreasing
  obtain ⟨_, _, q, _, _, below⟩ := M.stageThreeCondition_lower_bound c I0 I1 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F first second infinite choice rows hI0 hI1 nodeOrder closed seq whole decreasing
  exact ⟨q, below⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
