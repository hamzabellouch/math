import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneAssignmentImages

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
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
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.stageOneAssignmentActionGraph a s b d T T2 valid valid2
local notation "image" => M.stageOneAssignmentImage a s b d T T2 valid valid2
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem stageOneAssignment_fixed (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (indexFixed : refinementIndexCode ∅ (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val =
      refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
    (fixedU : a.act s g u = u) (fixedW : a.act s g w = w) :
    let x := stageOneAssignment
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
    ZFSet.pair x x ∈ graph g := by
  apply (M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround
    g C E U Rf Rc u w index hu hw _).2
  rw [indexFixed, fixedU, fixedW]

theorem stageOneAssignment_fixed_of_anchor_le (D : L) (g : G)
    (actor : g ∈ d.principalFix D) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (anchor : E ≤ D)
    (fixedU : a.act s g u = u) (fixedW : a.act s g w = w) :
    let x := stageOneAssignment
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val
    ZFSet.pair x x ∈ graph g := by
  obtain ⟨lower, domain, fine, coarse, _⟩ :=
    (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order ∅ T T2 valid familyGround C E U Rf Rc).1 index
  have atE : g ∈ d.principalFix E := d.principalFix_antitone anchor actor
  exact M.stageOneAssignment_fixed a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    g C E U Rf Rc u w index hu hw
    (M.niceRefinementIndex_fixed a s b d ∅ T T2 C E U.val Rf.val Rc.val
      lower.le domain fine coarse g atE) fixedU fixedW

theorem stageOneAssignmentImage_eq_of_fixed (g : G) {A : ZFSet.{u}}
    (subset : A ⊆ J) (fixed : ∀ x ∈ A, ZFSet.pair x x ∈ graph g) : image g A = A := by
  have function : FunctionGraphOn J (graph g) := ⟨J,
    M.stageOneAssignmentActionGraph_function a s b d T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround g⟩
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A J (graph g) y).1 hy
    exact (function.unique entry (fixed x hx)).symm ▸ hx
  · intro hy
    exact (mem_relationImage A J (graph g) y).2 ⟨subset hy, y, hy, fixed y hy⟩

theorem stageOneAssignmentImage_eq_of_anchor_le (D : L) (g : G)
    (actor : g ∈ d.principalFix D) {A : ZFSet.{u}} (subset : A ⊆ J)
    (bounds : ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s),
      refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I →
      u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode ∅ (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      E ≤ D ∧ a.act s g u = u ∧ a.act s g w = w) : image g A = A := by
  apply M.stageOneAssignmentImage_eq_of_fixed a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g subset
  intro x hx
  obtain ⟨idx, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 (subset hx)
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d ∅ T T2 valid valid2 hi
  let u : Name s := ⟨rawU, valid rawU hu⟩
  let w : Name s := ⟨rawW, valid rawW hw⟩
  obtain ⟨anchor, fixedU, fixedW⟩ := bounds C E U Rf Rc u w hi hu hw hx
  exact M.stageOneAssignment_fixed_of_anchor_le a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    D g actor C E U Rf Rc u w hi hu hw anchor fixedU fixedW

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "anchors" => refinementIndexFieldGraph I b.carrier 2

theorem stageOneDataBounds_assignment_fixes (S mu X tuples A : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g : G) (actor : g ∈ d.principalFix D) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (member : ZFSet.pair (stageOneAssignment
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val)
      (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) :
    E ≤ D ∧ a.act s g u = u ∧ a.act s g w = w := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, edge, lower, tupleU, tupleW, boundU, boundW⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder anchors tuples
      _ u.val w.val (b.encode D)).1 member
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![∅, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 edge).2.2
  subst rawE
  exact ⟨(b.pair_mem_conditionOrder E D).1 lower,
    support fu hfu u tupleU boundU actor, support fw hfw w tupleW boundW actor⟩

variable (valid2 : ∀ z ∈ T2, IsName s z) (t : Presentation G)
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

theorem stageOneAssignmentImage_eq_of_dataBound (S mu X tuples : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g : G) (actor : g ∈ d.principalFix D) {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T)
    (bound : ∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) :
    M.stageOneAssignmentImage a s b d T T2 valid valid2 g A = A := by
  apply M.stageOneAssignmentImage_eq_of_anchor_le a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround D g actor subset
  intro C E U Rf Rc u w _ _ _ member
  exact M.stageOneDataBounds_assignment_fixes a s b d T T2 valid S mu X tuples A D support
    g actor C E U Rf Rc u w (bound _ member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
