import OAI.SetTheory.PartitionPrinciple.Geometry.RefinementLevelThreeUnionGuards

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem stageThreeAssignments_disjoint {I0 I1 I2 T : ZFSet.{u}}
    (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2)) :
    ∀ z, z ∈ stageOneAssignments (I0 ∪ I1) T → z ∈ stageOneAssignments I2 T → False := by
  intro z old new
  obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments (I0 ∪ I1) T z).1 old
  have other := ((stageOneAssignment_mem_assignments I2 T i u w).1 new).1
  have apart := first.three_levels_disjoint second third
  rcases ZFSet.mem_union.1 hi with h0 | h1
  · exact apart.2.1 i ⟨h0,other⟩
  · exact apart.2.2 i ⟨h1,other⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1]
variable [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0) (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "J" => stageOneAssignments ((I0 ∪ I1) ∪ I2) T

noncomputable def stageThreeAssignmentActionGraph (g : G) : ZFSet.{u} :=
  M.stageTwoAssignmentActionGraph a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g ∪
    M.refinementAssignmentActionGraph a2 s2 b d (natSetCode 2) T T2 v2 v22 g

noncomputable def stageThreeAssignmentImage (g : G) (A : ZFSet.{u}) : ZFSet.{u} :=
  M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A ∪
    M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22 g A

theorem stageThreeAssignmentImage_subset (g : G) (A : ZFSet.{u}) :
    M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 g A ⊆ J := by
  rw [stageOneAssignments_union]
  intro z member
  rcases ZFSet.mem_union.1 member with old | new
  · exact ZFSet.mem_union.2 (Or.inl (M.stageTwoAssignmentImage_subset a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A old))
  · exact ZFSet.mem_union.2 (Or.inr (M.refinementAssignmentImage_subset a2 s2 b d (natSetCode 2) T T2 v2 v22 g A new))

theorem stageThreeAssignmentImage_mono (g : G) {A B : ZFSet.{u}} (subset : A ⊆ B) :
    M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 g A ⊆
      M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 g B := by
  intro z member
  rcases ZFSet.mem_union.1 member with old | new
  · exact ZFSet.mem_union.2 (Or.inl (M.stageTwoAssignmentImage_mono a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g subset old))
  · exact ZFSet.mem_union.2 (Or.inr (M.refinementAssignmentImage_mono a2 s2 b d (natSetCode 2) T T2 v2 v22 g subset new))

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P0 P1 P2 L : Type u}
variable [Group G] [PartialOrder P0] [OrderTop P0] [PartialOrder P1] [OrderTop P1] [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G P0) (s0 : Presentation P0)
variable (a1 : PosetAction G P1) (s1 : Presentation P1)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s2.carrier ∈ M.sets) (order : s2.conditionOrder ∈ M.sets)
variable (maps : a2.conditionMapFamily s2 t ∈ M.sets) (hT : T ∈ M.sets)
variable (closed : ∀ g (w : Name s2), w.val ∈ T → (a2.act s2 g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s2), w.val ∈ T2 → (a2.act s2 g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T v2).val ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a2 s2 b d base directed T v2)
variable (first : RefinementIndexLevelCode (M.niceRefinementIndices a0 s0 b d ∅ T T2 v0) ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1) (natSetCode 1))
variable (third : RefinementIndexLevelCode
  (M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2) (natSetCode 2))
include maps closed closed2 familyGround first second third

theorem stageThreeTests_image_iff (g : G) (A : ZFSet.{u}) (p : P2) :
    M.refinementLevelTests s2 pairing unions powers separation collection carrier order hT v2
      a2 b d base directed system (natSetCode 2) T2
        (M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 g A) (a2.iso g p) ↔
    M.refinementLevelTests s2 pairing unions powers separation collection carrier order hT v2
      a2 b d base directed system (natSetCode 2) T2 A p := by
  have union := M.refinementLevelTests_stageThreeUnion s2 pairing unions powers separation collection
    carrier order hT v2 a2 b d base directed system first second third
    (M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A)
    (M.refinementAssignmentImage a2 s2 b d (natSetCode 2) T T2 v2 v22 g A) (a2.iso g p)
    (M.stageTwoAssignmentImage_subset a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g A)
  exact union.trans (M.refinementLevelTests_image_iff a2 s2 b d (natSetCode 2) T T2 v2 v22 t
    pairing unions powers separation collection carrier order maps hT closed closed2 familyGround
    base directed system g A p)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
