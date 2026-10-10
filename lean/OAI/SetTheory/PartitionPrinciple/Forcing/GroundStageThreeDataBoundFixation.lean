import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoActionInputs

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.refinementAssignmentActionGraph a s b d level T T2 valid valid2
local notation "image" => M.refinementAssignmentImage a s b d level T T2 valid valid2
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem refinementAssignment_fixed (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (indexFixed : refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val =
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
    (fixedU : a.act s g u = u) (fixedW : a.act s g w = w) :
    let x := stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
    ZFSet.pair x x ∈ graph g := by
  apply (M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround
    g C E U Rf Rc u w index hu hw _).2
  rw [indexFixed, fixedU, fixedW]

theorem refinementAssignment_fixed_of_anchor_le (D : L) (g : G)
    (actor : g ∈ d.principalFix D) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (anchor : E ≤ D)
    (fixedU : a.act s g u = u) (fixedW : a.act s g w = w) :
    let x := stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
    ZFSet.pair x x ∈ graph g := by
  obtain ⟨lower, domain, fine, coarse, _⟩ :=
    (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T T2 valid familyGround C E U Rf Rc).1 index
  have atE : g ∈ d.principalFix E := d.principalFix_antitone anchor actor
  exact M.refinementAssignment_fixed a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    g C E U Rf Rc u w index hu hw
    (M.niceRefinementIndex_fixed a s b d level T T2 C E U.val Rf.val Rc.val
      lower.le domain fine coarse g atE) fixedU fixedW

theorem refinementAssignmentImage_eq_of_fixed (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ J) (fixed : ∀ x ∈ A, ZFSet.pair x x ∈ graph g) : image g A = A := by
  have function : FunctionGraphOn J (graph g) := ⟨J,
    M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround g⟩
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A J (graph g) y).1 hy
    exact (function.unique entry (fixed x hx)).symm ▸ hx
  · intro hy
    exact (mem_relationImage A J (graph g) y).2 ⟨subset hy, y, hy, fixed y hy⟩

theorem refinementAssignmentImage_eq_of_anchor_le (D : L) (g : G)
    (actor : g ∈ d.principalFix D) {A : ZFSet.{u}} (subset : A ⊆ J)
    (bounds : ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s),
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I →
      u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      E ≤ D ∧ a.act s g u = u ∧ a.act s g w = w) : image g A = A := by
  apply M.refinementAssignmentImage_eq_of_fixed a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g subset
  intro x hx
  obtain ⟨idx, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 (subset hx)
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
  let u : Name s := ⟨rawU, valid rawU hu⟩
  let w : Name s := ⟨rawW, valid rawW hw⟩
  obtain ⟨anchor, fixedU, fixedW⟩ := bounds C E U Rf Rc u w hi hu hw hx
  exact M.refinementAssignment_fixed_of_anchor_le a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    D g actor C E U Rf Rc u w hi hu hw anchor fixedU fixedW

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (I level T : ZFSet.{u})
local notation "anchors" => refinementIndexFieldGraph I b.carrier 2

omit [OrderTop P] in
theorem refinementDataBounds_assignment_fixes (S mu X tuples A : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g : G) (actor : g ∈ d.principalFix D) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (member : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val)
      (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) :
    E ≤ D ∧ a.act s g u = u ∧ a.act s g w = w := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, edge, lower, tupleU, tupleW, boundU, boundW⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder anchors tuples
      _ u.val w.val (b.encode D)).1 member
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 edge).2.2
  subst rawE
  exact ⟨(b.pair_mem_conditionOrder E D).1 lower,
    support fu hfu u tupleU boundU actor, support fw hfw w tupleW boundW actor⟩

variable (T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem refinementAssignment_fixed_of_dataBound (S mu X tuples A : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g : G) (actor : g ∈ d.principalFix D) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (member : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val)
      (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) :
    let z := stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
    ZFSet.pair z z ∈ M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g := by
  obtain ⟨anchor, fixedU, fixedW⟩ := M.refinementDataBounds_assignment_fixes a s b d I level T
    S mu X tuples A D support g actor C E U Rf Rc u w member
  exact M.refinementAssignment_fixed_of_anchor_le a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    D g actor C E U Rf Rc u w index hu hw anchor fixedU fixedW

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "J" => stageOneAssignments (I0 ∪ I1) T
local notation "graph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "image" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "laws0" => M.refinementAssignment_relationLaws a0 s0 b d ∅ T T2 v0 v02 t
  pairing unions powers separation collection carrier0 order0 params0
local notation "laws1" => M.refinementAssignment_relationLaws a1 s1 b d (natSetCode 1) T T2 v1 v12 t
  pairing unions powers separation collection carrier1 order1 params1
include pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1

variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
include first second

theorem stageTwoAssignmentImage_eq_of_fixed (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ J) (fixed : ∀ z ∈ A, ZFSet.pair z z ∈ graph g) : image g A = A := by
  rw [M.stageTwoAssignmentImage_eq_relationImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1]
  have function : FunctionGraphOn J (graph g) := ⟨J,
    (M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
      first second).function g⟩
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, z, hz, entry⟩ := (mem_relationImage A J (graph g) y).1 member
    exact (function.unique entry (fixed z hz)).symm ▸ hz
  · intro hy
    exact (mem_relationImage A J (graph g) y).2 ⟨subset hy, y, hy, fixed y hy⟩

theorem stageTwoAssignmentImage_eq_of_dataBound (S mu X tuples : ZFSet.{u}) (D : L)
    (support0 : ∀ f ∈ S, ∀ u : Name s0, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a0.stabilizer s0 u)
    (support1 : ∀ f ∈ S, ∀ u : Name s1, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a1.stabilizer s1 u)
    (g : G) (actor : g ∈ d.principalFix D) {A : ZFSet.{u}} (subset : A ⊆ J)
    (bound : ∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
      stageOneDataBounds A (I0 ∪ I1) T S b.carrier mu X b.conditionOrder
        (refinementIndexFieldGraph (I0 ∪ I1) b.carrier 2) tuples) : image g A = A := by
  apply M.stageTwoAssignmentImage_eq_of_fixed a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
    first second g subset
  intro z hz
  obtain ⟨idx, hi, rawU, hu, rawW, hw, rfl⟩ :=
    (mem_stageOneAssignments (I0 ∪ I1) T z).1 (subset hz)
  rcases ZFSet.mem_union.1 hi with hi | hi
  · obtain ⟨C,E,U,Rf,Rc,rfl⟩ := M.exists_niceRefinementIndex_fields a0 s0 b d ∅ T T2 v0 v02 hi
    let u : Name s0 := ⟨rawU, v0 rawU hu⟩
    let w : Name s0 := ⟨rawW, v0 rawW hw⟩
    apply ZFSet.mem_union.2
    left
    exact M.refinementAssignment_fixed_of_dataBound a0 s0 b d (I0 ∪ I1) ∅ T T2 v0 v02 t
      pairing unions powers separation collection carrier0 order0 params0.condition_maps
      params0.terms_closed params0.pairs_closed params0.family_ground
      S mu X tuples A D support0 g actor C E U Rf Rc u w hi hu hw (bound _ hz)
  · obtain ⟨C,E,U,Rf,Rc,rfl⟩ := M.exists_niceRefinementIndex_fields a1 s1 b d (natSetCode 1) T T2 v1 v12 hi
    let u : Name s1 := ⟨rawU, v1 rawU hu⟩
    let w : Name s1 := ⟨rawW, v1 rawW hw⟩
    apply ZFSet.mem_union.2
    right
    exact M.refinementAssignment_fixed_of_dataBound a1 s1 b d (I0 ∪ I1) (natSetCode 1) T T2 v1 v12 t
      pairing unions powers separation collection carrier1 order1 params1.condition_maps
      params1.terms_closed params1.pairs_closed params1.family_ground
      S mu X tuples A D support1 g actor C E U Rf Rc u w hi hu hw (bound _ hz)

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a0 : PosetAction G R) (s0 c : Presentation R)
variable (a1 : PosetAction G P) (s1 : Presentation P)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "image" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system1 : NiceNameSystem M a1 s1 b d base directed T v1)
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
variable (inputs : StageTwoConditionActionInputs M c
  (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) a1 s1 b d T T2 v1
  pairing unions powers separation collection carrier1 order1 hT base directed system1 a0
  (M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12))
local notation "Condition" => StageTwoCondition M c I0 a1 s1 b d T T2 v1
  pairing unions powers separation collection carrier1 order1 hT base directed system1
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a1 s1 b d T T2 v1
  pairing unions powers separation collection carrier1 order1 hT base directed system1
local notation "smallAct" => M.stageTwoSmallAction c I0 a1 s1 b d T T2 v1
  pairing unions powers separation collection carrier1 order1 hT base directed system1 a0 image inputs
include carrier0 order0 params0 params1 first second

theorem stageTwoSmallAction_fixed_of_dataBound (S mu X tuples : ZFSet.{u}) (D : L)
    (support0 : ∀ f ∈ S, ∀ u : Name s0, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a0.stabilizer s0 u)
    (support1 : ∀ f ∈ S, ∀ u : Name s1, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a1.stabilizer s1 u) :
    letI := smallOrder
    ∀ (g : G) (_actor : g ∈ d.principalFix D) (q : Shrink Condition),
      a0.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row →
      (∀ z ∈ ((equivShrink Condition).symm q).assignments,
        ZFSet.pair z (b.encode D) ∈ stageOneDataBounds ((equivShrink Condition).symm q).assignments
          (I0 ∪ I1) T S b.carrier mu X b.conditionOrder
          (refinementIndexFieldGraph (I0 ∪ I1) b.carrier 2) tuples) →
      (smallAct).iso g q = q := by
  let := smallOrder
  intro g actor q row bound
  apply (M.stageTwoSmallAction_fixed_iff c I0 a1 s1 b d T T2 v1
    pairing unions powers separation collection carrier1 order1 hT base directed system1 a0 image inputs g q).2
  refine ⟨row, ?_⟩
  exact M.stageTwoAssignmentImage_eq_of_dataBound a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
    S mu X tuples D support0 support1 g actor
    ((M.mem_groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega _).1
      ((equivShrink Condition).symm q).assignments_mem).2.1 bound

end

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
variable (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
variable (carrier2 : s2.carrier ∈ M.sets) (order2 : s2.conditionOrder ∈ M.sets)
variable (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
variable (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
variable (params2 : StageOneActionParameters M a2 s2 t b d T T2 v2)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "Jold" => stageOneAssignments (I0 ∪ I1) T
local notation "Jnew" => stageOneAssignments I2 T
local notation "J" => stageOneAssignments ((I0 ∪ I1) ∪ I2) T
local notation "graph" => M.stageThreeAssignmentActionGraph a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "image" => M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "oldGraph" => M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "oldImage" => M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12
local notation "newGraph" => M.refinementAssignmentActionGraph a2 s2 b d (natSetCode 2) T T2 v2 v22
local notation "newImage" => M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
local notation "oldLaws" => M.stageTwoAssignment_relationLaws a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
  pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1 first second
local notation "newLaws" => M.refinementAssignment_relationLaws a2 s2 b d (natSetCode 2) T T2 v2 v22 t
  pairing unions powers separation collection carrier2 order2 params2

variable (third : RefinementIndexLevelCode (M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2) (natSetCode 2))
include pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
  params0 params1 params2 first second third

theorem stageThreeAssignmentImage_eq_of_fixed (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ J) (fixed : ∀ z ∈ A, ZFSet.pair z z ∈ graph g) : image g A = A := by
  rw [M.stageThreeAssignmentImage_eq_relationImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second]
  have function : FunctionGraphOn J (graph g) := ⟨J,
    (M.stageThreeAssignment_relationLaws a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
      params0 params1 params2 first second third).function g⟩
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, z, hz, entry⟩ := (mem_relationImage A J (graph g) y).1 member
    exact (function.unique entry (fixed z hz)).symm ▸ hz
  · intro hy
    exact (mem_relationImage A J (graph g) y).2 ⟨subset hy, y, hy, fixed y hy⟩

theorem stageThreeAssignmentImage_eq_of_dataBound (S mu X tuples : ZFSet.{u}) (D : L)
    (support0 : ∀ f ∈ S, ∀ u : Name s0, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a0.stabilizer s0 u)
    (support1 : ∀ f ∈ S, ∀ u : Name s1, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a1.stabilizer s1 u)
    (support2 : ∀ f ∈ S, ∀ u : Name s2, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a2.stabilizer s2 u)
    (g : G) (actor : g ∈ d.principalFix D) {A : ZFSet.{u}} (subset : A ⊆ J)
    (bound : ∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
      stageOneDataBounds A ((I0 ∪ I1) ∪ I2) T S b.carrier mu X b.conditionOrder
        (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) b.carrier 2) tuples) : image g A = A := by
  apply M.stageThreeAssignmentImage_eq_of_fixed a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
    pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
    params0 params1 params2 first second third g subset
  intro z hz
  obtain ⟨idx, hi, rawU, hu, rawW, hw, rfl⟩ :=
    (mem_stageOneAssignments ((I0 ∪ I1) ∪ I2) T z).1 (subset hz)
  rcases ZFSet.mem_union.1 hi with old | hi
  · rcases ZFSet.mem_union.1 old with hi | hi
    · obtain ⟨C,E,U,Rf,Rc,rfl⟩ := M.exists_niceRefinementIndex_fields a0 s0 b d ∅ T T2 v0 v02 hi
      let u : Name s0 := ⟨rawU, v0 rawU hu⟩
      let w : Name s0 := ⟨rawW, v0 rawW hw⟩
      apply ZFSet.mem_union.2
      left
      apply ZFSet.mem_union.2
      left
      exact M.refinementAssignment_fixed_of_dataBound a0 s0 b d ((I0 ∪ I1) ∪ I2) ∅ T T2 v0 v02 t
        pairing unions powers separation collection carrier0 order0 params0.condition_maps
        params0.terms_closed params0.pairs_closed params0.family_ground
        S mu X tuples A D support0 g actor C E U Rf Rc u w hi hu hw (bound _ hz)
    · obtain ⟨C,E,U,Rf,Rc,rfl⟩ := M.exists_niceRefinementIndex_fields a1 s1 b d (natSetCode 1) T T2 v1 v12 hi
      let u : Name s1 := ⟨rawU, v1 rawU hu⟩
      let w : Name s1 := ⟨rawW, v1 rawW hw⟩
      apply ZFSet.mem_union.2
      left
      apply ZFSet.mem_union.2
      right
      exact M.refinementAssignment_fixed_of_dataBound a1 s1 b d ((I0 ∪ I1) ∪ I2) (natSetCode 1) T T2 v1 v12 t
        pairing unions powers separation collection carrier1 order1 params1.condition_maps
        params1.terms_closed params1.pairs_closed params1.family_ground
        S mu X tuples A D support1 g actor C E U Rf Rc u w hi hu hw (bound _ hz)
  · obtain ⟨C,E,U,Rf,Rc,rfl⟩ := M.exists_niceRefinementIndex_fields a2 s2 b d (natSetCode 2) T T2 v2 v22 hi
    let u : Name s2 := ⟨rawU, v2 rawU hu⟩
    let w : Name s2 := ⟨rawW, v2 rawW hw⟩
    apply ZFSet.mem_union.2
    right
    exact M.refinementAssignment_fixed_of_dataBound a2 s2 b d ((I0 ∪ I1) ∪ I2) (natSetCode 2) T T2 v2 v22 t
      pairing unions powers separation collection carrier2 order2 params2.condition_maps
      params2.terms_closed params2.pairs_closed params2.family_ground
      S mu X tuples A D support2 g actor C E U Rf Rc u w hi hu hw (bound _ hz)

end PartitionPilot.Forcing.TransitiveGround

end OAI
