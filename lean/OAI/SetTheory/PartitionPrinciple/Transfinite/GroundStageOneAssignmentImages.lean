import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRefinementAssignmentActionFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.stageOneAssignmentActionGraph a s b d T T2 valid valid2

noncomputable def stageOneAssignmentImage (g : G) (A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A J (graph g)

theorem stageOneAssignmentImage_subset (g : G) (A : ZFSet.{u}) :
    M.stageOneAssignmentImage a s b d T T2 valid valid2 g A ⊆ J :=
  fun y h => ((mem_relationImage A J (graph g) y).1 h).1

theorem stageOneAssignmentImage_mono (g : G) {A B : ZFSet.{u}} (subset : A ⊆ B) :
    M.stageOneAssignmentImage a s b d T T2 valid valid2 g A ⊆
      M.stageOneAssignmentImage a s b d T T2 valid valid2 g B := by
  intro y hy
  obtain ⟨hy, x, hx, entry⟩ := (mem_relationImage A J (graph g) y).1 hy
  exact (mem_relationImage B J (graph g) y).2 ⟨hy, x, subset hx, entry⟩

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

include pairing unions powers separation collection carrier order maps closed closed2 familyGround in
theorem stageOneAssignmentActionGraph_injection (g : G) : InjectionCode J J (graph g) :=
  relationProduct_injection
    (M.niceRefinementIndexActionGraph_injection a s b d ∅ T T2 valid valid2 t
      pairing unions powers separation collection carrier order maps closed closed2 familyGround g)
    (relationProduct_injection (stageOneTermAction_injection a s T valid closed g)
      (stageOneTermAction_injection a s T valid closed g))

include pairing unions powers separation collection carrier order maps closed closed2 familyGround in
theorem stageOneAssignmentImage_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (A : ZFSet.{u}) :
    stageOneAssignment (refinementIndexCode ∅ (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val ∈
        M.stageOneAssignmentImage a s b d T T2 valid valid2 g A ↔
    stageOneAssignment (refinementIndexCode ∅ (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A := by
  have entry := (M.stageOneAssignmentActionGraph_entry a s b d T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 familyGround
    g C E U Rf Rc u w index hu hw _).2 rfl
  have injection := M.stageOneAssignmentActionGraph_injection a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g
  constructor
  · intro hy
    obtain ⟨_, x, hx, xy⟩ := (mem_relationImage A J (graph g) _).1 hy
    have equal := injection.injective _ _ _ xy entry
    exact equal ▸ hx
  · intro hx
    exact (mem_relationImage A J (graph g) _).2
      ⟨(ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2, _, hx, entry⟩

include pairing unions powers separation collection carrier order maps closed closed2 familyGround in
theorem stageOneAssignmentImage_small
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI : I ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (g : G) {A : ZFSet.{u}}
    (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
    M.stageOneAssignmentImage a s b d T T2 valid valid2 g A ∈ M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hA, subset, small⟩ := (M.mem_groundSmallSubsets J ZFSet.omega A).1 member
  have hJ := M.stageOneAssignments_mem pairing unions powers separation hI hT
  have hg := M.stageOneAssignmentActionGraph_mem a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier maps nodeMaps hT hT2 hI g
  have injection := M.stageOneAssignmentActionGraph_injection a s b d T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g
  exact (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.relationImage_mem separation hA hJ hg,
      M.stageOneAssignmentImage_subset a s b d T T2 valid valid2 g A,
      M.groundEmbeddable_image pairing unions powers separation hA hJ omega hg injection subset small⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
