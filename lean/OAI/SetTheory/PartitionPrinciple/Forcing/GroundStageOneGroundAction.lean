import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneDataBoundFixation
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneFlatConditions

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
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
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem stageOneAssignmentActionGraph_one {x : ZFSet.{u}} (hx : x ∈ J) (y : ZFSet.{u}) :
    ZFSet.pair x y ∈ graph 1 ↔ y = x := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d ∅ T T2 valid valid2 hi
  have termOne : (a.act s 1 ⟨u, valid u hu⟩).val = u :=
    congrArg (fun term : Name s => term.val) (a.act_one s ⟨u, valid u hu⟩)
  have wordOne : (a.act s 1 ⟨w, valid w hw⟩).val = w :=
    congrArg (fun term : Name s => term.val) (a.act_one s ⟨w, valid w hw⟩)
  simpa only [d.one, a.act_one, termOne, wordOne] using
    M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround 1 C E U Rf Rc
      ⟨u, valid u hu⟩ ⟨w, valid w hw⟩ hi hu hw y

theorem stageOneAssignmentActionGraph_mul (g h : G) {x : ZFSet.{u}} (hx : x ∈ J) (z : ZFSet.{u}) :
    ZFSet.pair x z ∈ graph (g * h) ↔
      ∃ y ∈ J, ZFSet.pair x y ∈ graph h ∧ ZFSet.pair y z ∈ graph g := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d ∅ T T2 valid valid2 hi
  let nu : Name s := ⟨u, valid u hu⟩
  let nw : Name s := ⟨w, valid w hw⟩
  have indexH := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps ∅ T T2 valid closed closed2 familyGround h C E U Rf Rc).mpr hi
  let y := stageOneAssignment (refinementIndexCode ∅ (b.encode (d.iso h C)) (b.encode (d.iso h E))
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val)
    (a.act s h nu).val (a.act s h nw).val
  have hy : y ∈ J := (stageOneAssignment_mem_assignments I T _ _ _).2
    ⟨indexH, closed h nu hu, closed h nw hw⟩
  have atH := M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround h C E U Rf Rc nu nw hi hu hw
  have atG := M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround g
    (d.iso h C) (d.iso h E) (move h U) (move h Rf) (move h Rc)
    (a.act s h nu) (a.act s h nw) indexH (closed h nu hu) (closed h nw hw) z
  have atMul := M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround (g * h)
    C E U Rf Rc nu nw hi hu hw z
  simp only [M.stageOneNameAction_val] at atG
  have same : ZFSet.pair (stageOneAssignment
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u w) z ∈ graph (g * h) ↔
      ZFSet.pair y z ∈ graph g := by
    dsimp only [y]
    rw [atMul, atG]
    simp only [d.mul, a.act_mul]
  constructor
  · intro entry
    exact ⟨y, hy, (atH y).mpr rfl, same.mp entry⟩
  · rintro ⟨y', _, eh, eg⟩
    have equal : y' = y := (atH y').mp eh
    exact same.mpr (equal ▸ eg)

theorem stageOneAssignmentImage_one {A : ZFSet.{u}} (subset : A ⊆ J) : image 1 A = A := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A J (graph 1) y).1 hy
    exact (M.stageOneAssignmentActionGraph_one a s b d T T2 valid valid2 t pairing unions powers
      separation collection carrier order maps closed closed2 familyGround (subset hx) y).mp entry ▸ hx
  · intro hy
    exact (mem_relationImage A J (graph 1) y).2 ⟨subset hy, y, hy,
      (M.stageOneAssignmentActionGraph_one a s b d T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround (subset hy) y).mpr rfl⟩

theorem stageOneAssignmentImage_mul (g h : G) {A : ZFSet.{u}} (subset : A ⊆ J) :
    image (g * h) A = image g (image h A) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A J (graph (g * h)) z).1 hz
    obtain ⟨y, hy, eh, eg⟩ :=
      (M.stageOneAssignmentActionGraph_mul a s b d T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround g h (subset hx) z).mp entry
    exact (mem_relationImage (image h A) J (graph g) z).2
      ⟨hz, y, (mem_relationImage A J (graph h) y).2 ⟨hy, x, hx, eh⟩, eg⟩
  · intro hz
    obtain ⟨hz, y, hy, eg⟩ := (mem_relationImage (image h A) J (graph g) z).1 hz
    obtain ⟨hy, x, hx, eh⟩ := (mem_relationImage A J (graph h) y).1 hy
    exact (mem_relationImage A J (graph (g * h)) z).2 ⟨hz, x, hx,
      (M.stageOneAssignmentActionGraph_mul a s b d T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround g h (subset hx) z).mpr ⟨y, hy, eh, eg⟩⟩

end TransitiveGround

namespace TransitiveGround
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
variable (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps

include maps closed closed2 familyGround in
theorem stageOneTests_image_iff (g : G) (A : ZFSet.{u}) (p : P) :
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 (M.stageOneAssignmentImage a s b d T T2 valid valid2 g A) (a.iso g p) ↔
    M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A p := by
  have term (w : (M.nameDomain s).names) : (move g w).val.val ∈ T ↔ w.val.val ∈ T := by
    constructor
    · intro member
      have original := closed g⁻¹ (a.act s g w.val) member
      simpa only [a.act_inv_left] using original
    · exact closed g w.val
  have index := M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps ∅ T T2 valid closed closed2 familyGround g
  have image := M.stageOneAssignmentImage_entry a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g
  have single := M.stageOneSingleTests_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g
  have collision := M.stageOneCollisionTest_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed g
  constructor
  · intro tests C E U Rf Rc
    dsimp only
    intro member
    obtain ⟨hs, hc⟩ := tests (d.iso g C) (d.iso g E) (move g U) (move g Rf) (move g Rc)
      ((index C E U Rf Rc).mpr member)
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      exact (single C E U Rf Rc u w p).mp
        (hs (move g u) (move g w) ((term u).mpr hu) ((term w).mpr hw)
          ((image C E U Rf Rc u.val w.val member hu hw A).mpr entry))
    · intro u u' w w' hu hu' hw hw' entry entry'
      exact (collision Rf Rc u u' w w' p).mp
        (hc (move g u) (move g u') (move g w) (move g w')
          ((term u).mpr hu) ((term u').mpr hu') ((term w).mpr hw) ((term w').mpr hw')
          ((image C E U Rf Rc u.val w.val member hu hw A).mpr entry)
          ((image C E U Rf Rc u'.val w'.val member hu' hw' A).mpr entry'))
  · intro tests C E U Rf Rc
    obtain ⟨C, rfl⟩ := (d.iso g).surjective C
    obtain ⟨E, rfl⟩ := (d.iso g).surjective E
    obtain ⟨U, rfl⟩ := (move g).surjective U
    obtain ⟨Rf, rfl⟩ := (move g).surjective Rf
    obtain ⟨Rc, rfl⟩ := (move g).surjective Rc
    dsimp only
    intro member
    have old := (index C E U Rf Rc).mp member
    obtain ⟨hs, hc⟩ := tests C E U Rf Rc old
    refine ⟨?_, ?_⟩
    · intro u w hu hw entry
      obtain ⟨u, rfl⟩ := (move g).surjective u
      obtain ⟨w, rfl⟩ := (move g).surjective w
      have hu := (term u).mp hu
      have hw := (term w).mp hw
      exact (single C E U Rf Rc u w p).mpr
        (hs u w hu hw ((image C E U Rf Rc u.val w.val old hu hw A).mp entry))
    · intro u u' w w' hu hu' hw hw' entry entry'
      obtain ⟨u, rfl⟩ := (move g).surjective u
      obtain ⟨u', rfl⟩ := (move g).surjective u'
      obtain ⟨w, rfl⟩ := (move g).surjective w
      obtain ⟨w', rfl⟩ := (move g).surjective w'
      have hu := (term u).mp hu
      have hu' := (term u').mp hu'
      have hw := (term w).mp hw
      have hw' := (term w').mp hw'
      exact (collision Rf Rc u u' w w' p).mpr
        (hc u u' w w' hu hu' hw hw'
          ((image C E U Rf Rc u.val w.val old hu hw A).mp entry)
          ((image C E U Rf Rc u'.val w'.val old hu' hw' A).mp entry'))

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
local notation "Q" => M.stageOneForcing a c b d T T2 valid
local notation "J" => stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T
local notation "B" => M.groundSmallSubsets J ZFSet.omega
local notation "assignmentFamily" => M.stageOneAssignmentActionFamily a c.pairEmpty t b d T T2 valid valid2

noncomputable def stageOneFullActionGraph : ZFSet.{u} :=
  rowAssignmentActionGraph t.carrier Q c.carrier B J (a.conditionMapFamily c t) assignmentFamily

theorem stageOneFullActionGraph_entry (g : G) (p q : P) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode p) A)) (ZFSet.pair (c.encode q) D) ∈
      M.stageOneFullActionGraph a c t b d T T2 valid valid2 ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ ZFSet.pair (c.encode q) D ∈ Q ∧ a.iso g p = q ∧
        D = M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g A := by
  rw [stageOneFullActionGraph, pair_mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨_,source,target,_,_,_,_,rf,af,indexed,row,indexedA,image⟩
    have rowEq := (a.pair_mem_conditionMapFamily c t g rf).1 indexed
    have assignmentEq := (M.pair_mem_stageOneAssignmentActionFamily a c.pairEmpty t b d
      T T2 valid valid2 g af).1 indexedA
    rw [assignmentEq] at image
    exact ⟨source,target,(c.pair_mem_graph c (a.iso g) p q).1 (rowEq ▸ row),image⟩
  · rintro ⟨source,target,moved,image⟩
    have sourceBound := ZFSet.pair_mem_prod.1 ((M.mem_stageOneConditions c.carrier _ _).1 source).1
    have targetBound := ZFSet.pair_mem_prod.1 ((M.mem_stageOneConditions c.carrier _ _).1 target).1
    exact ⟨t.encode_mem g,source,target,sourceBound.1,sourceBound.2,targetBound.1,targetBound.2,
      _,_,(a.pair_mem_conditionMapFamily c t g _).2 rfl,
      (c.pair_mem_graph c (a.iso g) p q).2 moved,
      (M.pair_mem_stageOneAssignmentActionFamily a c.pairEmpty t b d T T2 valid valid2 g _).2 rfl,image⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
include pairing unions powers separation carrier order nodes hT indices system

theorem stageOneFullActionGraph_mem (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (group : t.carrier ∈ M.sets) (rowMaps : a.conditionMapFamily c t ∈ M.sets)
    (assignmentMaps : assignmentFamily ∈ M.sets) :
    M.stageOneFullActionGraph a c t b d T T2 valid valid2 ∈ M.sets := by
  have conditions := M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT
  exact M.rowAssignmentActionGraph_mem pairing unions powers separation group conditions carrier
    (M.groundSmallSubsets_mem powers separation assignments omega) assignments rowMaps assignmentMaps

end TransitiveGround

section
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
variable (valid2 : ∀ z ∈ T2, IsName s z) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (hT2 : T2 ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d ∅ T T2 valid ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)

namespace StageOneCondition
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2
local notation "J" => stageOneAssignments (M.niceRefinementIndices a s b d ∅ T T2 valid) T
local notation "image" => M.stageOneAssignmentImage a s b d T T2 valid valid2

noncomputable def act (g : G) (p : Condition) : Condition where
  row := a.iso g p.row
  assignments := image g p.assignments
  assignments_mem := M.stageOneAssignmentImage_small a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    nodeMaps hT hT2 indexGround omega g p.assignments_mem
  tests := (M.stageOneTests_image_iff a s b d T T2 valid valid2 t pairing unions powers separation
    collection carrier order maps hT closed closed2 familyGround base directed system g p.assignments p.row).mpr p.tests

local notation "act'" => act M s pairing unions powers separation collection carrier order hT valid
  a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega

theorem act_fields (g : G) (p : Condition) :
    (act' g p).row = a.iso g p.row ∧ (act' g p).assignments = image g p.assignments := ⟨rfl, rfl⟩

theorem act_one (p : Condition) : act' 1 p = p := by
  apply ext M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2
  · exact a.one p.row
  · exact M.stageOneAssignmentImage_one a s b d T T2 valid valid2 t pairing unions powers separation
      collection carrier order maps closed closed2 familyGround
      ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).mp p.assignments_mem).2.1

theorem act_mul (g h : G) (p : Condition) : act' (g * h) p = act' g (act' h p) := by
  apply ext M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2
  · exact a.mul g h p.row
  · exact M.stageOneAssignmentImage_mul a s b d T T2 valid valid2 t pairing unions powers separation
      collection carrier order maps closed closed2 familyGround g h
      ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).mp p.assignments_mem).2.1

theorem act_inv_left (g : G) (p : Condition) : act' g⁻¹ (act' g p) = p := by
  rw [← act_mul M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega,
    inv_mul_cancel, act_one]

theorem act_inv_right (g : G) (p : Condition) : act' g (act' g⁻¹ p) = p := by
  rw [← act_mul M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega,
    mul_inv_cancel, act_one]

theorem act_le_iff (g : G) (p q : Condition) : act' g p ≤ act' g q ↔ p ≤ q := by
  have mono : ∀ g (p q : Condition), p ≤ q → act' g p ≤ act' g q := by
    intro g p q below
    exact ⟨(a.iso g).monotone below.1,
      M.stageOneAssignmentImage_mono a s b d T T2 valid valid2 g below.2⟩
  constructor
  · intro below
    have back := mono g⁻¹ _ _ below
    simpa only [act_inv_left] using back
  · exact mono g p q

noncomputable def actOrderIso (g : G) : Condition ≃o Condition where
  toFun := act' g
  invFun := act' g⁻¹
  left_inv := act_inv_left M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega g
  right_inv := act_inv_right M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega g
  map_rel_iff' := act_le_iff M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega g _ _

noncomputable def posetAction : PosetAction G Condition where
  iso := actOrderIso M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega
  one := act_one M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega
  mul := act_mul M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega

end StageOneCondition
end

namespace TransitiveGround
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
variable (collection : CollectionSchema M.sets) (t : Presentation G)
variable (inputs : StageOneActionParameters M a c.pairEmpty t b d T T2 valid)
variable (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "typedAct" => StageOneCondition.act M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2 valid2 t inputs.condition_maps
  inputs.node_maps hT2 inputs.terms_closed inputs.pairs_closed inputs.family_ground indices.index_ground omega

noncomputable def stageOneSmallAction :
    letI := smallOrder
    PosetAction G (Shrink Condition) := by
  letI := smallOrder
  let original := StageOneCondition.posetAction M c.pairEmpty pairing unions powers separation collection
    pairedCarrier pairedOrder hT valid a b d base directed system T2 valid2 t inputs.condition_maps
    inputs.node_maps hT2 inputs.terms_closed inputs.pairs_closed inputs.family_ground indices.index_ground omega
  let e := M.stageOneConditionOrderIso a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection
  exact {
    iso := fun g => (e.symm.trans (original.iso g)).trans e
    one := by
      intro q
      change e (original.iso 1 (e.symm q)) = q
      rw [original.one, e.apply_symm_apply]
    mul := by
      intro g h q
      change e (original.iso (g * h) (e.symm q)) =
        e (original.iso g (e.symm (e (original.iso h (e.symm q)))))
      rw [e.symm_apply_apply, original.mul] }

local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega

theorem stageOneSmallAction_decode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (equivShrink Condition).symm ((smallAct).iso g q) =
        typedAct g ((equivShrink Condition).symm q) := by
  let := smallOrder
  intro g q
  change (equivShrink Condition).symm
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact (equivShrink Condition).symm_apply_apply _

theorem stageOneSmallAction_encode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (pres).encode ((smallAct).iso g q) =
        ZFSet.pair (c.encode (a.iso g ((equivShrink Condition).symm q).row))
          (M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g
            ((equivShrink Condition).symm q).assignments) := by
  let := smallOrder
  intro g q
  change (pres).encode
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact M.stageOneConditionPresentation_encode a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection _

end TransitiveGround

section
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
variable (valid2 : ∀ z ∈ T2, IsName s z) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (hT2 : T2 ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d ∅ T T2 valid ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)

namespace StageOneCondition
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "J" => stageOneAssignments I T
local notation "image" => M.stageOneAssignmentImage a s b d T T2 valid valid2
local notation "act'" => act M s pairing unions powers separation collection carrier order hT valid
  a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega
local notation "action" => posetAction M s pairing unions powers separation collection carrier order hT valid
  a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround indexGround omega

theorem act_eq_iff (g : G) (p : Condition) :
    act' g p = p ↔ a.iso g p.row = p.row ∧ image g p.assignments = p.assignments := by
  constructor
  · intro same
    exact ⟨congrArg (fun q : Condition => q.row) same,
      congrArg (fun q : Condition => q.assignments) same⟩
  · rintro ⟨row, assignments⟩
    exact ext M s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 row assignments

theorem posetAction_fixed (g : G) (p : Condition)
    (row : a.iso g p.row = p.row) (assignments : image g p.assignments = p.assignments) :
    (action).iso g p = p :=
  (act_eq_iff M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround
    indexGround omega g p).2 ⟨row, assignments⟩

theorem act_fixed_of_anchor_le (D : L) (g : G) (actor : g ∈ d.principalFix D) (p : Condition)
    (row : a.iso g p.row = p.row)
    (bounds : ∀ (C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s),
      refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I →
      u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode ∅ (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ p.assignments →
      E ≤ D ∧ a.act s g u = u ∧ a.act s g w = w) : act' g p = p := by
  apply (act_eq_iff M s pairing unions powers separation collection carrier order hT valid
    a b d base directed system T2 valid2 t maps nodeMaps hT2 closed closed2 familyGround
    indexGround omega g p).2
  exact ⟨row, M.stageOneAssignmentImage_eq_of_anchor_le a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround
    D g actor ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).1 p.assignments_mem).2.1 bounds⟩

end StageOneCondition
end

namespace TransitiveGround
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
variable (collection : CollectionSchema M.sets) (t : Presentation G)
variable (inputs : StageOneActionParameters M a c.pairEmpty t b d T T2 valid)
variable (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "typedAct" => StageOneCondition.act M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2 valid2 t inputs.condition_maps
  inputs.node_maps hT2 inputs.terms_closed inputs.pairs_closed inputs.family_ground indices.index_ground omega

local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "fullGraph" => M.stageOneFullActionGraph a c t b d T T2 valid valid2

theorem stageOneSmallActionGraph_eq :
    letI := smallOrder
    (smallAct).actionGraph (pres) t = fullGraph := by
  let := smallOrder
  have encoded (g : G) (x : Shrink Condition) := M.stageOneSmallAction_encode a c b d T T2 valid
    pairing unions powers separation carrier order nodes hT indices base directed system collection t inputs hT2 omega g x
  have meaning (g : G) (x y : Shrink Condition) :
      ZFSet.pair (ZFSet.pair (t.encode g) ((pres).encode x)) ((pres).encode y) ∈ fullGraph ↔
      (smallAct).iso g x = y := by
    change ZFSet.pair (ZFSet.pair (t.encode g)
      (ZFSet.pair (c.encode ((equivShrink Condition).symm x).row)
        ((equivShrink Condition).symm x).assignments))
      (ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
        ((equivShrink Condition).symm y).assignments) ∈ fullGraph ↔ _
    rw [M.stageOneFullActionGraph_entry]
    constructor
    · rintro ⟨_,_,rowEqual,assignmentEqual⟩
      apply (pres).injective
      rw [encoded]
      change ZFSet.pair (c.encode (a.iso g ((equivShrink Condition).symm x).row))
        (M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g
          ((equivShrink Condition).symm x).assignments) =
        ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
          ((equivShrink Condition).symm y).assignments
      rw [rowEqual, assignmentEqual]
    · intro equal
      have codeEqual := congrArg (pres).encode equal
      rw [encoded] at codeEqual
      change ZFSet.pair (c.encode (a.iso g ((equivShrink Condition).symm x).row))
        (M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g
          ((equivShrink Condition).symm x).assignments) =
        ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
          ((equivShrink Condition).symm y).assignments at codeEqual
      obtain ⟨rowEqual,assignmentEqual⟩ := ZFSet.pair_injective codeEqual
      exact ⟨(pres).encode_mem x,(pres).encode_mem y,c.injective rowEqual,assignmentEqual.symm⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨⟨g,x⟩,rfl⟩ := ((t.product (pres)).mem_graph (pres) (fun gx => (smallAct).iso gx.1 gx.2) z).1 member
    exact (meaning g x ((smallAct).iso g x)).2 rfl
  · intro member
    have boundMember := member
    unfold stageOneFullActionGraph rowAssignmentActionGraph at boundMember
    have bounds : z ∈ ZFSet.prod (ZFSet.prod t.carrier (pres).carrier) (pres).carrier :=
      (ZFSet.mem_sep.1 boundMember).1
    obtain ⟨source,hSource,y,hy,rfl⟩ := ZFSet.mem_prod.1 bounds
    obtain ⟨g,hg,x,hx,rfl⟩ := ZFSet.mem_prod.1 hSource
    obtain ⟨g,rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x,rfl⟩ := ((pres).mem_carrier x).1 hx
    obtain ⟨y,rfl⟩ := ((pres).mem_carrier y).1 hy
    exact ((smallAct).triple_mem_actionGraph (pres) t g x y).2 ((meaning g x y).1 member)

variable (nodeOrder : b.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (originalMaps : a.conditionMapFamily c t ∈ M.sets)
include nodeOrder group originalMaps

theorem stageOneSmallActionGraph_mem :
    letI := smallOrder
    (smallAct).actionGraph (pres) t ∈ M.sets := by
  let := smallOrder
  rw [M.stageOneSmallActionGraph_eq a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega]
  have assignmentMaps := M.stageOneAssignmentActionFamily_mem_of_inputs a c.pairEmpty t b d T T2 valid valid2
    pairing unions powers separation collection pairedCarrier group nodes pairedOrder inputs.condition_maps
    inputs.node_maps hT hT2 indices.index_ground inputs.terms_closed inputs.pairs_closed inputs.family_ground
  exact M.stageOneFullActionGraph_mem a c t b d T T2 valid valid2 pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega group originalMaps assignmentMaps

theorem stageOneSmallActionMapFamily_mem :
    letI := smallOrder
    (smallAct).conditionMapFamily (pres) t ∈ M.sets := by
  let := smallOrder
  exact M.conditionMapFamily_mem_of_actionGraph (smallAct) (pres) t pairing unions powers separation collection
    (M.stageOneConditionPresentation_carrier_mem a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection nodeOrder omega) group
    (M.stageOneSmallActionGraph_mem a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega nodeOrder group originalMaps)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
