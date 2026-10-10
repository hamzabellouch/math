import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementAssignmentImages

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
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
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
include pairing unions powers separation collection carrier order maps closed closed2 familyGround

theorem refinementAssignmentActionGraph_one {x : ZFSet.{u}} (hx : x ∈ J) (y : ZFSet.{u}) :
    ZFSet.pair x y ∈ graph 1 ↔ y = x := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
  have entry := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround 1 C E U Rf Rc
    ⟨u, valid u hu⟩ ⟨w, valid w hw⟩ hi hu hw y
  rw [a.act_one s ⟨u, valid u hu⟩, a.act_one s ⟨w, valid w hw⟩] at entry
  simpa only [d.one, a.act_one] using entry

theorem refinementAssignmentActionGraph_mul (g h : G) {x : ZFSet.{u}} (hx : x ∈ J) (z : ZFSet.{u}) :
    ZFSet.pair x z ∈ graph (g * h) ↔
      ∃ y ∈ J, ZFSet.pair x y ∈ graph h ∧ ZFSet.pair y z ∈ graph g := by
  obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
  let nu : Name s := ⟨u, valid u hu⟩
  let nw : Name s := ⟨w, valid w hw⟩
  have indexH := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 familyGround h C E U Rf Rc).mpr hi
  let y := stageOneAssignment (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
    (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val)
    (a.act s h nu).val (a.act s h nw).val
  have hy : y ∈ J := (stageOneAssignment_mem_assignments I T _ _ _).2
    ⟨indexH, closed h nu hu, closed h nw hw⟩
  have atH := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround h C E U Rf Rc nu nw hi hu hw
  have atG := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround g
    (d.iso h C) (d.iso h E) (move h U) (move h Rf) (move h Rc)
    (a.act s h nu) (a.act s h nw) indexH (closed h nu hu) (closed h nw hw) z
  have atMul := M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround (g * h)
    C E U Rf Rc nu nw hi hu hw z
  simp only [M.stageOneNameAction_val] at atG
  have same : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u w) z ∈ graph (g * h) ↔
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

theorem refinementAssignmentImage_one {A : ZFSet.{u}} (subset : A ⊆ J) : image 1 A = A := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A J (graph 1) y).1 hy
    exact (M.refinementAssignmentActionGraph_one a s b d level T T2 valid valid2 t pairing unions powers
      separation collection carrier order maps closed closed2 familyGround (subset hx) y).mp entry ▸ hx
  · intro hy
    exact (mem_relationImage A J (graph 1) y).2 ⟨subset hy, y, hy,
      (M.refinementAssignmentActionGraph_one a s b d level T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround (subset hy) y).mpr rfl⟩

theorem refinementAssignmentImage_mul (g h : G) {A : ZFSet.{u}} (subset : A ⊆ J) :
    image (g * h) A = image g (image h A) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A J (graph (g * h)) z).1 hz
    obtain ⟨y, hy, eh, eg⟩ :=
      (M.refinementAssignmentActionGraph_mul a s b d level T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround g h (subset hx) z).mp entry
    exact (mem_relationImage (image h A) J (graph g) z).2
      ⟨hz, y, (mem_relationImage A J (graph h) y).2 ⟨hy, x, hx, eh⟩, eg⟩
  · intro hz
    obtain ⟨hz, y, hy, eg⟩ := (mem_relationImage (image h A) J (graph g) z).1 hz
    obtain ⟨hy, x, hx, eh⟩ := (mem_relationImage A J (graph h) y).1 hy
    exact (mem_relationImage A J (graph (g * h)) z).2 ⟨hz, x, hx,
      (M.refinementAssignmentActionGraph_mul a s b d level T T2 valid valid2 t pairing unions powers
        separation collection carrier order maps closed closed2 familyGround g h (subset hx) z).mpr ⟨y, hy, eh, eg⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
