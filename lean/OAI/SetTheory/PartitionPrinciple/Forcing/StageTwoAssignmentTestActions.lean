import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementAssignmentImages
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementRawTestMonotonicity

namespace OAI

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
variable (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps

include maps closed closed2 familyGround in
theorem refinementLevelTests_image_iff (g : G) (A : ZFSet.{u}) (p : P) :
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) (a.iso g p) ↔
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system level T2 A p := by
  have term (w : (M.nameDomain s).names) : (move g w).val.val ∈ T ↔ w.val.val ∈ T := by
    constructor
    · intro member
      have original := closed g⁻¹ (a.act s g w.val) member
      simpa only [a.act_inv_left] using original
    · exact closed g w.val
  have index := M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 familyGround g
  have image := M.refinementAssignmentImage_entry a s b d level T T2 valid valid2 t
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

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem stageOneAssignments_union (I0 I1 T : ZFSet.{u}) :
    stageOneAssignments (I0 ∪ I1) T = stageOneAssignments I0 T ∪ stageOneAssignments I1 T := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments (I0 ∪ I1) T z).1 member
    rcases ZFSet.mem_union.1 hi with left | right
    · exact ZFSet.mem_union.2 (Or.inl ((stageOneAssignment_mem_assignments I0 T i u w).2 ⟨left,hu,hw⟩))
    · exact ZFSet.mem_union.2 (Or.inr ((stageOneAssignment_mem_assignments I1 T i u w).2 ⟨right,hu,hw⟩))
  · intro member
    rcases ZFSet.mem_union.1 member with left | right
    · obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments I0 T z).1 left
      exact (stageOneAssignment_mem_assignments (I0 ∪ I1) T i u w).2 ⟨ZFSet.mem_union.2 (Or.inl hi),hu,hw⟩
    · obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments I1 T z).1 right
      exact (stageOneAssignment_mem_assignments (I0 ∪ I1) T i u w).2 ⟨ZFSet.mem_union.2 (Or.inr hi),hu,hw⟩

theorem stageTwoAssignments_disjoint {I0 I1 T : ZFSet.{u}}
    (first : RefinementIndexLevelCode I0 ∅) (second : RefinementIndexLevelCode I1 (natSetCode 1)) :
    ∀ z, z ∈ stageOneAssignments I0 T → z ∈ stageOneAssignments I1 T → False := by
  intro z left right
  obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments I0 T z).1 left
  have other := ((stageOneAssignment_mem_assignments I1 T i u w).1 right).1
  exact first.disjoint second (fun equal => Nat.zero_ne_one (natSetCode_injective equal)) i ⟨hi,other⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "J" => stageOneAssignments (I0 ∪ I1) T

noncomputable def stageTwoAssignmentActionGraph (g : G) : ZFSet.{u} :=
  M.refinementAssignmentActionGraph a0 s0 b d ∅ T T2 v0 v02 g ∪
    M.refinementAssignmentActionGraph a1 s1 b d (natSetCode 1) T T2 v1 v12 g

noncomputable def stageTwoAssignmentImage (g : G) (A : ZFSet.{u}) : ZFSet.{u} :=
  M.refinementAssignmentImage a0 s0 b d ∅ T T2 v0 v02 g A ∪
    M.refinementAssignmentImage a1 s1 b d (natSetCode 1) T T2 v1 v12 g A

theorem stageTwoAssignmentImage_subset (g : G) (A : ZFSet.{u}) :
    M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A ⊆ J := by
  rw [stageOneAssignments_union]
  intro z member
  rcases ZFSet.mem_union.1 member with left | right
  · exact ZFSet.mem_union.2 (Or.inl (M.refinementAssignmentImage_subset a0 s0 b d ∅ T T2 v0 v02 g A left))
  · exact ZFSet.mem_union.2 (Or.inr (M.refinementAssignmentImage_subset a1 s1 b d (natSetCode 1) T T2 v1 v12 g A right))

theorem stageTwoAssignmentImage_mono (g : G) {A B : ZFSet.{u}} (subset : A ⊆ B) :
    M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A ⊆
      M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g B := by
  intro z member
  rcases ZFSet.mem_union.1 member with left | right
  · exact ZFSet.mem_union.2 (Or.inl (M.refinementAssignmentImage_mono a0 s0 b d ∅ T T2 v0 v02 g subset left))
  · exact ZFSet.mem_union.2 (Or.inr (M.refinementAssignmentImage_mono a1 s1 b d (natSetCode 1) T T2 v1 v12 g subset right))

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0)
variable (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s1.carrier ∈ M.sets) (order : s1.conditionOrder ∈ M.sets)
variable (maps : a1.conditionMapFamily s1 t ∈ M.sets) (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s1), w.val ∈ T → (a1.act s1 g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s1), w.val ∈ T2 → (a1.act s1 g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T v1).val ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a1 s1 b d base directed T v1)
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
include maps closed closed2 familyGround first second

theorem stageTwoTests_image_iff (g : G) (A : ZFSet.{u}) (p : P1) :
    M.refinementLevelTests s1 pairing unions powers separation collection carrier order hT v1
      a1 b d base directed system (natSetCode 1) T2
        (M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A) (a1.iso g p) ↔
    M.refinementLevelTests s1 pairing unions powers separation collection carrier order hT v1
      a1 b d base directed system (natSetCode 1) T2 A p := by
  have union := M.refinementLevelTests_stageTwoUnion s1 pairing unions powers separation collection
    carrier order hT v1 a1 b d base directed system first second
    (M.refinementAssignmentImage a0 s0 b d ∅ T T2 v0 v02 g A)
    (M.refinementAssignmentImage a1 s1 b d (natSetCode 1) T T2 v1 v12 g A) (a1.iso g p)
    (M.refinementAssignmentImage_subset a0 s0 b d ∅ T T2 v0 v02 g A)
  exact union.trans (M.refinementLevelTests_image_iff a1 s1 b d (natSetCode 1) T T2 v1 v12 t
    pairing unions powers separation collection carrier order maps hT closed closed2 familyGround
    base directed system g A p)

end PartitionPilot.Forcing.TransitiveGround

end OAI
