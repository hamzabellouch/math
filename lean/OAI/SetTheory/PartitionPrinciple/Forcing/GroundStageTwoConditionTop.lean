import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundBinaryRowStageOneRefinement

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid

structure StageTwoCondition where
  row : R
  assignments : ZFSet.{u}
  assignments_mem : assignments ∈
    M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega
  lower : P
  lower_code : s.encode lower = ZFSet.pair (c.encode row)
    (assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) assignments)
  tests : M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
    a b d base directed system (natSetCode 1) T2 assignments lower

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

@[ext] theorem ext {p q : Condition}
    (rows : p.row = q.row) (data : p.assignments = q.assignments) : p = q := by
  cases p with
  | mk rp Ap smallp lp codep testp =>
    cases q with
    | mk rq Aq smallq lq codeq testq =>
      dsimp only at rows data
      subst rq
      subst Aq
      have equal : lp = lq := s.injective (codep.trans codeq.symm)
      subst lq
      rfl

noncomputable def code (p : Condition) : ZFSet.{u} := ZFSet.pair (c.encode p.row) p.assignments

theorem code_eq_iff (p q : Condition) :
    code M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system p =
    code M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system q ↔ p.row = q.row ∧ p.assignments = q.assignments := by
  unfold code
  rw [ZFSet.pair_inj]
  exact and_congr c.injective.eq_iff Iff.rfl

theorem code_injective : Function.Injective (code M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system) := by
  intro p q equal
  obtain ⟨rows, data⟩ := (code_eq_iff M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system p q).1 equal
  exact ext M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system rows data

theorem code_mem_candidateBound (p : Condition) :
    code M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system p ∈ M.stageOneCandidateBound c.carrier (I0 ∪ I1) T :=
  ZFSet.pair_mem_prod.2 ⟨c.encode_mem p.row, p.assignments_mem⟩

instance small : Small.{u} Condition := by
  let bound := M.stageOneCandidateBound c.carrier (I0 ∪ I1) T
  let f : Condition → bound := fun p =>
    ⟨code M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system p,
      code_mem_candidateBound M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system p⟩
  apply small_of_injective (f := f)
  intro p q equal
  exact code_injective M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system (congrArg Subtype.val equal)

end StageTwoCondition

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

include nodes indices in
theorem stageTwoConditionCode_mem (p : Condition) : code p ∈ Q :=
  (M.stageTwoForcing_entry c.carrier I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system (c.encode p.row) p.assignments).2
    ⟨c.encode_mem p.row, p.assignments_mem, p.lower, p.lower_code, p.tests⟩

include nodes indices in
theorem exists_stageTwoConditionCode {z : ZFSet.{u}} (member : z ∈ Q) :
    ∃ p : Condition, code p = z := by
  have candidate := (M.mem_stageTwoConditions c.carrier
    (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid)
    (stageTwoAssignmentLevels I0 (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
    (natSetCode 1) (M.refinementLevelFormulaData a s b d (natSetCode 1) T T2 valid) z).1 member
  obtain ⟨row, A, small, equal⟩ := M.exists_stageOneCandidate_fields c _ _ candidate.1
  obtain ⟨_, _, lower, lowerCode, tests⟩ :=
    (M.stageTwoForcing_entry c.carrier I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system (c.encode row) A).1
      (equal ▸ member)
  exact ⟨⟨row, A, small, lower, lowerCode, tests⟩, equal.symm⟩

noncomputable def stageTwoConditionPresentation : Presentation (Shrink Condition) where
  carrier := Q
  encode x := code ((equivShrink Condition).symm x)
  injective := (StageTwoCondition.code_injective M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system).comp
      (equivShrink Condition).symm.injective
  mem_carrier z := by
    constructor
    · intro member
      obtain ⟨p, equal⟩ := M.exists_stageTwoConditionCode c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order nodes hT indices base directed system member
      exact ⟨equivShrink Condition p, by simpa only [Equiv.symm_apply_apply] using equal⟩
    · rintro ⟨x, equal⟩
      exact equal ▸ M.stageTwoConditionCode_mem c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order nodes hT indices base directed system
        ((equivShrink Condition).symm x)

theorem stageTwoConditionPresentation_encode (p : Condition) :
    (M.stageTwoConditionPresentation c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system).encode (equivShrink Condition p) =
      code p :=
  congrArg code ((equivShrink Condition).symm_apply_apply p)

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

instance partialOrder : PartialOrder Condition where
  le p q := p.row ≤ q.row ∧ q.assignments ⊆ p.assignments
  le_refl _ := ⟨le_rfl, fun _ h => h⟩
  le_trans _ _ _ first second := ⟨first.1.trans second.1, fun _ h => first.2 (second.2 h)⟩
  le_antisymm p q first second := by
    apply ext M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system (le_antisymm first.1 second.1)
    apply ZFSet.ext
    intro z
    exact ⟨fun h => second.2 h, fun h => first.2 h⟩

theorem le_iff (p q : Condition) :
    p ≤ q ↔ p.row ≤ q.row ∧ q.assignments ⊆ p.assignments := Iff.rfl

def rowProjection : Condition →o R where
  toFun p := p.row
  monotone' _ _ below := below.1

end StageTwoCondition
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

@[instance_reducible] noncomputable def stageTwoConditionSmallOrder : PartialOrder (Shrink Condition) where
  le p q := (equivShrink Condition).symm p ≤ (equivShrink Condition).symm q
  le_refl _ := le_rfl
  le_trans _ _ _ first second := first.trans second
  le_antisymm _ _ first second := (equivShrink Condition).symm.injective (le_antisymm first second)

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

noncomputable def stageTwoConditionOrderIso :
    letI := smallOrder
    Condition ≃o Shrink Condition := by
  letI := smallOrder
  exact {
    toEquiv := equivShrink Condition
    map_rel_iff' := by
      intro p q
      change (equivShrink Condition).symm (equivShrink Condition p) ≤
        (equivShrink Condition).symm (equivShrink Condition q) ↔ p ≤ q
      simp only [Equiv.symm_apply_apply] }

noncomputable def stageTwoFlatConditionSystem :
    letI := smallOrder
    FlatConditionSystem M c pres
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T) := by
  letI := smallOrder
  exact {
    row := fun p => ((equivShrink Condition).symm p).row
    assignments := fun p => ((equivShrink Condition).symm p).assignments
    encode := fun _ => rfl
    le_iff := fun _ _ => Iff.rfl
    assignments_mem := fun p => ((equivShrink Condition).symm p).assignments_mem }

theorem stageTwoConditionOrder_mem
    (hRow : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
    (rowOrder : c.conditionOrder ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    (pres).conditionOrder ∈ M.sets := by
  let := smallOrder
  have ground := M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid
    pairing unions powers separation hRow hI0 hT carrier order nodes nodeOrder valid2
    indices base directed system omega
  exact (M.stageTwoFlatConditionSystem c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system).conditionOrder_mem
      pairing unions powers separation hRow ground
      (M.stageOneAssignments_mem pairing unions powers separation
        (M.binary_union_mem pairing unions hI0 indices.index_ground) hT) omega rowOrder

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "levels" => stageTwoAssignmentLevels I0
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

theorem lower_row (p : Condition) : F.row p.lower = p.row := by
  have equal := (F.encode p.lower).symm.trans p.lower_code
  exact c.injective (ZFSet.pair_inj.1 equal).1

theorem lower_assignments (p : Condition) :
    F.assignments p.lower = assignmentCut levels (natSetCode 1) p.assignments := by
  exact (ZFSet.pair_inj.1 ((F.encode p.lower).symm.trans p.lower_code)).2

def restriction : Condition →o P where
  toFun p := p.lower
  monotone' := by
    intro p q below
    apply (F.le_iff p.lower q.lower).2
    constructor
    · rw [lower_row M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system F p,
        lower_row M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system F q]
      exact below.1
    · rw [lower_assignments M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system F p,
        lower_assignments M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system F q]
      exact assignmentCut_mono below.2

end StageTwoCondition

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "levels" => stageTwoAssignmentLevels I0
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))

noncomputable def includeLower (q : P) : Condition := by
  have facts :=
    (M.mem_groundSmallSubsets (stageOneAssignments I0 T) ZFSet.omega (F.assignments q)).1
      (F.assignments_mem q)
  have ground := facts.1
  have subsetOld := facts.2.1
  have small := facts.2.2
  refine ⟨F.row q, F.assignments q, ?_, q, ?_, ?_⟩
  · apply (M.mem_groundSmallSubsets _ _ _).2
    refine ⟨ground, ?_, small⟩
    intro z hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ :=
      (mem_stageOneAssignments I0 T z).1 (subsetOld hz)
    exact (stageOneAssignment_mem_assignments _ T t u w).2
      ⟨ZFSet.mem_union.2 (Or.inl ht), hu, hw⟩
  · rw [stageTwoAssignmentCut_one_eq first second subsetOld]
    exact F.encode q
  · exact M.refinementLevelTests_stageTwoOld s pairing unions powers separation collection
      carrier order hT valid a b d base directed system first second q subsetOld

local notation "inc" => includeLower M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "restrict" => restriction M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F

theorem includeLower_lower (q : P) : (inc q).lower = q := rfl

theorem includeLower_code (q : P) :
    code M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system (inc q) = s.encode q :=
  (F.encode q).symm

noncomputable def inclusion : P ↪o Condition where
  toFun := inc
  inj' _ _ equal := congrArg StageTwoCondition.lower equal
  map_rel_iff' := by
    intro p q
    exact (F.le_iff p q).symm

theorem restriction_inclusion (q : P) :
    restrict (inclusion M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system F first second q) = q := rfl

theorem le_inclusion_iff (p : Condition) (q : P) :
    p ≤ inclusion M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system F first second q ↔ restrict p ≤ q := by
  change p.row ≤ F.row q ∧ F.assignments q ⊆ p.assignments ↔ p.lower ≤ q
  rw [F.le_iff, lower_row M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F p,
    lower_assignments M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F p]
  apply and_congr_right
  intro _
  have subsetOld := ((M.mem_groundSmallSubsets _ _ (F.assignments q)).1
    (F.assignments_mem q)).2.1
  constructor
  · intro subset
    rw [stageTwoAssignmentCut_one first second]
    exact fun z hz => ZFSet.mem_sep.2 ⟨subset hz, subsetOld hz⟩
  · intro subset
    exact fun _ hz => assignmentCut_subset _ _ _ (subset hz)

end StageTwoCondition

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "levels" => stageTwoAssignmentLevels I0
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)

noncomputable def splice (p : Condition) (q : P) (below : q ≤ p.lower) : Condition := by
  have old := (M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)
  have memberq : F.assignments q ∈ M.groundSmallSubsets
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
      ZFSet.omega := by
    apply (M.mem_groundSmallSubsets _ _ _).2
    refine ⟨old.1, ?_, old.2.2⟩
    intro z hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I0 T z).1 (old.2.1 hz)
    exact (stageOneAssignment_mem_assignments _ T t u w).2
      ⟨ZFSet.mem_union.2 (Or.inl ht), hu, hw⟩
  have graph := M.stageTwoAssignmentLevels_mem pairing unions powers separation hI0 hI1 hT
  have hOne := M.transitive (M.omega_mem separation infinite) (natSetCode_mem_omega 1)
  have lowerCut := stageTwoAssignmentSplice_lower_eq first second p.assignments old.2.1
  exact {
    row := F.row q
    assignments := assignmentSplice levels (natSetCode 1) (F.assignments q) p.assignments
    assignments_mem := M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation
      infinite choice graph hOne memberq p.assignments_mem
    lower := q
    lower_code := by rw [lowerCut]; exact F.encode q
    tests := (M.refinementLevelTests_stageTwoSplice s pairing unions powers separation collection
      carrier order hT valid a b d base directed system first second (F.assignments q) p.assignments q).2
      (M.refinementLevelTests_mono s pairing unions powers separation collection carrier order hT valid
        a b d base directed system (natSetCode 1) T2 p.assignments p.tests below) }

local notation "lifted" => splice M c I0 a s b d T T2 valid pairing unions powers separation collection
  carrier order hT base directed system F first second infinite choice hI0 hI1

theorem splice_row (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).row = F.row q := rfl

theorem splice_assignments (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).assignments =
      assignmentSplice levels (natSetCode 1) (F.assignments q) p.assignments := rfl

theorem splice_lower (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).lower = q := rfl

theorem splice_le (p : Condition) (q : P) (below : q ≤ p.lower) : lifted p q below ≤ p := by
  obtain ⟨rows, data⟩ := (F.le_iff q p.lower).1 below
  have lowerRow := lower_row M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F p
  have lowerData := lower_assignments M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F p
  refine ⟨rows.trans_eq lowerRow, ?_⟩
  change p.assignments ⊆ assignmentSplice levels (natSetCode 1) (F.assignments q) p.assignments
  apply assignmentSplice_extends
  rw [stageTwoAssignmentCut_one_eq first second
    ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1, ← lowerData]
  exact data

include first second infinite choice hI0 hI1 in
theorem exists_lift_restriction (p : Condition) (q : P) (below : q ≤ p.lower) :
    ∃ r : Condition, r ≤ p ∧ r.lower = q ∧ r.row = F.row q ∧
      r.assignments = assignmentSplice levels (natSetCode 1) (F.assignments q) p.assignments :=
  ⟨lifted p q below, splice_le M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F first second infinite choice hI0 hI1 p q below,
    rfl, rfl, rfl⟩

end StageTwoCondition
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

@[instance_reducible] noncomputable def stageTwoConditionTop : OrderTop Condition where
  top := inc ⊤
  le_top p := (StageTwoCondition.le_inclusion_iff M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system F first second p ⊤).2 le_top

@[instance_reducible] noncomputable def stageTwoConditionSmallTop :
    letI := smallOrder
    OrderTop (Shrink Condition) := by
  letI := smallOrder
  letI := M.stageTwoConditionTop c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order hT base directed system F first second
  exact {
    top := equivShrink Condition ⊤
    le_top p := by
      change (equivShrink Condition).symm p ≤ (equivShrink Condition).symm (equivShrink Condition ⊤)
      rw [Equiv.symm_apply_apply]
      exact le_top }

theorem stageTwoConditionPresentation_top :
    letI := smallOrder
    letI := M.stageTwoConditionSmallTop c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order hT base directed system F first second
    (pres).encode ⊤ = s.encode ⊤ := by
  let := smallOrder
  let := M.stageTwoConditionSmallTop c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order hT base directed system F first second
  change (pres).encode (equivShrink Condition (inc ⊤)) = s.encode ⊤
  rw [M.stageTwoConditionPresentation_encode c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system]
  exact StageTwoCondition.includeLower_code M c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order hT base directed system F first second ⊤

end TransitiveGround

end PartitionPilot.Forcing

end OAI
