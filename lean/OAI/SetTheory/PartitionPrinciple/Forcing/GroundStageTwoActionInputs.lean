import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoConditionTop
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageThreeAssignmentFamilies

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (rowAction : PosetAction G R) (t : Presentation G) (assignmentGraph : G → ZFSet.{u})
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid
local notation "J" => stageOneAssignments (I0 ∪ I1) T
local notation "B" => M.groundSmallSubsets J ZFSet.omega
local notation "assignmentFamily" => familyCodeGraph t.encode assignmentGraph

noncomputable def stageTwoFullActionGraph : ZFSet.{u} :=
  rowAssignmentActionGraph t.carrier Q c.carrier B J
    (rowAction.conditionMapFamily c t) assignmentFamily

theorem stageTwoFullActionGraph_entry (g : G) (p q : R) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode p) A)) (ZFSet.pair (c.encode q) D) ∈
      M.stageTwoFullActionGraph c I0 a s b d T T2 valid rowAction t assignmentGraph ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ ZFSet.pair (c.encode q) D ∈ Q ∧ rowAction.iso g p = q ∧
        D = relationImage A J (assignmentGraph g) := by
  rw [stageTwoFullActionGraph, pair_mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨_,source,target,_,_,_,_,rf,af,indexed,row,indexedA,image⟩
    have rowEq := (rowAction.pair_mem_conditionMapFamily c t g rf).1 indexed
    have assignmentEq := (pair_mem_familyCodeGraph t.encode assignmentGraph t.injective g af).1 indexedA
    rw [assignmentEq] at image
    exact ⟨source,target,(c.pair_mem_graph c (rowAction.iso g) p q).1 (rowEq ▸ row),image⟩
  · rintro ⟨source,target,moved,image⟩
    have sourceBound := (M.stageTwoForcing_raw_entry c.carrier I0 a s b d T T2 valid (c.encode p) A).1 source
    have targetBound := (M.stageTwoForcing_raw_entry c.carrier I0 a s b d T T2 valid (c.encode q) D).1 target
    exact ⟨t.encode_mem g,source,target,sourceBound.1,sourceBound.2.1,targetBound.1,targetBound.2.1,
      _,_,(rowAction.pair_mem_conditionMapFamily c t g _).2 rfl,
      (c.pair_mem_graph c (rowAction.iso g) p q).2 moved,
      (pair_mem_familyCodeGraph t.encode assignmentGraph t.injective g _).2 rfl,image⟩

theorem stageTwoFullActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets) (hT : T ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid)
    (omega : ZFSet.omega ∈ M.sets) (group : t.carrier ∈ M.sets)
    (rowMaps : rowAction.conditionMapFamily c t ∈ M.sets)
    (assignmentMaps : assignmentFamily ∈ M.sets) :
    M.stageTwoFullActionGraph c I0 a s b d T T2 valid rowAction t assignmentGraph ∈ M.sets := by
  have conditions := M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder valid2 indices
    base directed system omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hI0 indices.index_ground) hT
  exact M.rowAssignmentActionGraph_mem pairing unions powers separation group conditions rows
    (M.groundSmallSubsets_mem powers separation assignments omega) assignments rowMaps assignmentMaps

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoConditionActionInputs (M : TransitiveGround.{u})
    (c : Presentation R) (I0 : ZFSet.{u})
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid)
    (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u}) : Prop where
  small : ∀ g A, A ∈ M.groundSmallSubsets
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T) ZFSet.omega →
    image g A ∈ M.groundSmallSubsets
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T) ZFSet.omega
  one : ∀ A, A ⊆ stageOneAssignments
      (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T → image 1 A = A
  mul : ∀ g h A, A ⊆ stageOneAssignments
      (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T →
    image (g * h) A = image g (image h A)
  mono : ∀ g A B, A ⊆ B → image g A ⊆ image g B
  lower_code : ∀ g (p : StageTwoCondition M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system),
    s.encode (a.iso g p.lower) = ZFSet.pair (c.encode (rowAction.iso g p.row))
      (assignmentCut (stageTwoAssignmentLevels I0
        (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
        (natSetCode 1) (image g p.assignments))
  tests : ∀ g (p : StageTwoCondition M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system),
    M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 1) T2 (image g p.assignments) (a.iso g p.lower)

end

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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "J" => stageOneAssignments
  (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

noncomputable def act (g : G) (p : Condition) : Condition where
  row := rowAction.iso g p.row
  assignments := image g p.assignments
  assignments_mem := inputs.small g p.assignments p.assignments_mem
  lower := a.iso g p.lower
  lower_code := inputs.lower_code g p
  tests := inputs.tests g p

local notation "act'" => act M c I0 a s b d T T2 valid pairing unions powers separation collection
  carrier order hT base directed system rowAction image inputs

theorem act_fields (g : G) (p : Condition) :
    (act' g p).row = rowAction.iso g p.row ∧
      (act' g p).assignments = image g p.assignments ∧ (act' g p).lower = a.iso g p.lower :=
  ⟨rfl, rfl, rfl⟩

theorem act_one (p : Condition) : act' 1 p = p := by
  apply ext M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system
  · exact rowAction.one p.row
  · exact inputs.one p.assignments ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).1 p.assignments_mem).2.1

theorem act_mul (g h : G) (p : Condition) : act' (g * h) p = act' g (act' h p) := by
  apply ext M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system
  · exact rowAction.mul g h p.row
  · exact inputs.mul g h p.assignments ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).1 p.assignments_mem).2.1

theorem act_inv_left (g : G) (p : Condition) : act' g⁻¹ (act' g p) = p := by
  rw [← act_mul M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs, inv_mul_cancel, act_one]

theorem act_inv_right (g : G) (p : Condition) : act' g (act' g⁻¹ p) = p := by
  rw [← act_mul M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs, mul_inv_cancel, act_one]

theorem act_le_iff (g : G) (p q : Condition) : act' g p ≤ act' g q ↔ p ≤ q := by
  have mono : ∀ g (p q : Condition), p ≤ q → act' g p ≤ act' g q := by
    intro g p q below
    exact ⟨(rowAction.iso g).monotone below.1, inputs.mono g q.assignments p.assignments below.2⟩
  constructor
  · intro below
    have back := mono g⁻¹ _ _ below
    simpa only [act_inv_left] using back
  · exact mono g p q

noncomputable def actOrderIso (g : G) : Condition ≃o Condition where
  toFun := act' g
  invFun := act' g⁻¹
  left_inv := act_inv_left M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs g
  right_inv := act_inv_right M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs g
  map_rel_iff' := act_le_iff M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs g _ _

noncomputable def posetAction : PosetAction G Condition where
  iso := actOrderIso M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs
  one := act_one M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs
  mul := act_mul M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system rowAction image inputs

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
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system
local notation "typedAct" => StageTwoCondition.act M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

noncomputable def stageTwoSmallAction :
    letI := smallOrder
    PosetAction G (Shrink Condition) := by
  letI := smallOrder
  let original := StageTwoCondition.posetAction M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system rowAction image inputs
  let e := M.stageTwoConditionOrderIso c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system
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

local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

theorem stageTwoSmallAction_decode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (equivShrink Condition).symm ((smallAct).iso g q) =
        typedAct g ((equivShrink Condition).symm q) := by
  let := smallOrder
  intro g q
  change (equivShrink Condition).symm
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact (equivShrink Condition).symm_apply_apply _

theorem stageTwoSmallAction_encode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (pres).encode ((smallAct).iso g q) =
        ZFSet.pair (c.encode (rowAction.iso g ((equivShrink Condition).symm q).row))
          (image g ((equivShrink Condition).symm q).assignments) := by
  let := smallOrder
  intro g q
  change (pres).encode
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact M.stageTwoConditionPresentation_encode c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system _

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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "act'" => act M c I0 a s b d T T2 valid pairing unions powers separation collection
  carrier order hT base directed system rowAction image inputs

theorem act_eq_iff (g : G) (p : Condition) :
    act' g p = p ↔ rowAction.iso g p.row = p.row ∧ image g p.assignments = p.assignments := by
  constructor
  · intro same
    exact ⟨congrArg (fun q : Condition => q.row) same,
      congrArg (fun q : Condition => q.assignments) same⟩
  · rintro ⟨row, assignments⟩
    exact ext M c I0 a s b d T T2 valid pairing unions powers separation collection
      carrier order hT base directed system row assignments

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
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system
local notation "typedAct" => StageTwoCondition.act M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs
variable (t : Presentation G) (assignmentGraph : G → ZFSet.{u})
local notation "J" => stageOneAssignments
  (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T
variable (image_eq : ∀ g A, image g A = relationImage A
  (stageOneAssignments (I0 ∪ M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
  (assignmentGraph g))
local notation "fullGraph" => M.stageTwoFullActionGraph c I0 a s b d T T2 valid rowAction t assignmentGraph
include image_eq

theorem stageTwoSmallActionGraph_eq :
    letI := smallOrder
    (smallAct).actionGraph (pres) t = fullGraph := by
  let := smallOrder
  have encoded (g : G) (x : Shrink Condition) := M.stageTwoSmallAction_encode c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    rowAction image inputs g x
  have meaning (g : G) (x y : Shrink Condition) :
      ZFSet.pair (ZFSet.pair (t.encode g) ((pres).encode x)) ((pres).encode y) ∈ fullGraph ↔
      (smallAct).iso g x = y := by
    change ZFSet.pair (ZFSet.pair (t.encode g)
      (ZFSet.pair (c.encode ((equivShrink Condition).symm x).row)
        ((equivShrink Condition).symm x).assignments))
      (ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
        ((equivShrink Condition).symm y).assignments) ∈ fullGraph ↔ _
    rw [M.stageTwoFullActionGraph_entry, ← image_eq g]
    constructor
    · rintro ⟨_,_,rowEqual,assignmentEqual⟩
      apply (pres).injective
      rw [encoded]
      change ZFSet.pair (c.encode (rowAction.iso g ((equivShrink Condition).symm x).row))
        (image g ((equivShrink Condition).symm x).assignments) =
        ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
          ((equivShrink Condition).symm y).assignments
      rw [rowEqual, assignmentEqual]
    · intro equal
      have codeEqual := congrArg (pres).encode equal
      rw [encoded] at codeEqual
      change ZFSet.pair (c.encode (rowAction.iso g ((equivShrink Condition).symm x).row))
        (image g ((equivShrink Condition).symm x).assignments) =
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
    unfold stageTwoFullActionGraph rowAssignmentActionGraph at boundMember
    have bounds : z ∈ ZFSet.prod (ZFSet.prod t.carrier (pres).carrier) (pres).carrier :=
      (ZFSet.mem_sep.1 boundMember).1
    obtain ⟨source,hSource,y,hy,rfl⟩ := ZFSet.mem_prod.1 bounds
    obtain ⟨g,hg,x,hx,rfl⟩ := ZFSet.mem_prod.1 hSource
    obtain ⟨g,rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x,rfl⟩ := ((pres).mem_carrier x).1 hx
    obtain ⟨y,rfl⟩ := ((pres).mem_carrier y).1 hy
    exact ((smallAct).triple_mem_actionGraph (pres) t g x y).2 ((meaning g x y).1 member)

variable (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (rowMaps : rowAction.conditionMapFamily c t ∈ M.sets)
variable (assignmentMaps : familyCodeGraph t.encode assignmentGraph ∈ M.sets)
include rows hI0 nodeOrder omega group rowMaps assignmentMaps

theorem stageTwoSmallActionGraph_mem :
    letI := smallOrder
    (smallAct).actionGraph (pres) t ∈ M.sets := by
  let := smallOrder
  rw [M.stageTwoSmallActionGraph_eq c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    rowAction image inputs t assignmentGraph image_eq]
  exact M.stageTwoFullActionGraph_mem c I0 a s b d T T2 valid rowAction t assignmentGraph
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder valid2 indices
    base directed system omega group rowMaps assignmentMaps

theorem stageTwoSmallActionMapFamily_mem :
    letI := smallOrder
    (smallAct).conditionMapFamily (pres) t ∈ M.sets := by
  let := smallOrder
  have conditions := M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder valid2 indices
    base directed system omega
  exact M.conditionMapFamily_mem_of_actionGraph (smallAct) (pres) t
    pairing unions powers separation collection conditions group
    (M.stageTwoSmallActionGraph_mem c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      rowAction image inputs t assignmentGraph image_eq rows hI0 nodeOrder omega group rowMaps assignmentMaps)

end TransitiveGround

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
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

theorem stageTwoSmallAction_fixed_iff :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (smallAct).iso g q = q ↔
      rowAction.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row ∧
      image g ((equivShrink Condition).symm q).assignments = ((equivShrink Condition).symm q).assignments := by
  let := smallOrder
  intro g q
  have decoded := M.stageTwoSmallAction_decode c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system rowAction image inputs g q
  have typed := StageTwoCondition.act_eq_iff M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system rowAction image inputs
    g ((equivShrink Condition).symm q)
  constructor
  · intro same
    apply typed.1
    exact decoded.symm.trans (congrArg (equivShrink Condition).symm same)
  · intro fields
    apply (equivShrink Condition).symm.injective
    exact decoded.trans (typed.2 fields)

end TransitiveGround

namespace TransitiveGround
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

theorem stageTwoActionInputs
    (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
    (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
    (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
    (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (first : RefinementIndexLevelCode I0 ∅) (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (omega : ZFSet.omega ∈ M.sets)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system1 : NiceNameSystem M a1 s1 b d base directed T v1)
    (F : FlatConditionSystem M c s1 (stageOneAssignments I0 T))
    (row_equivariant : ∀ g q, F.row (a1.iso g q) = a0.iso g (F.row q))
    (data_equivariant : ∀ g q, F.assignments (a1.iso g q) =
      M.refinementAssignmentImage a0 s0 b d ∅ T T2 v0 v02 g (F.assignments q)) :
    StageTwoConditionActionInputs M c I0 a1 s1 b d T T2 v1
      pairing unions powers separation collection carrier1 order1 hT base directed system1 a0 image := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g A member
    exact M.stageTwoAssignmentImage_small a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
      first second hT hT2 hI0 hI1 omega g member
  · intro A subset
    exact M.stageTwoAssignmentImage_one a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
      first second subset
  · intro g h A subset
    exact M.stageTwoAssignmentImage_mul a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 params0 params1
      first second g h subset
  · intro g A B subset
    exact M.stageTwoAssignmentImage_mono a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g subset
  · intro g p
    rw [F.encode, row_equivariant, data_equivariant,
      StageTwoCondition.lower_row M c I0 a1 s1 b d T T2 v1 pairing unions powers separation
        collection carrier1 order1 hT base directed system1 F p,
      StageTwoCondition.lower_assignments M c I0 a1 s1 b d T T2 v1 pairing unions powers separation
        collection carrier1 order1 hT base directed system1 F p]
    exact congrArg (ZFSet.pair (c.encode (a0.iso g p.row))) (M.stageTwoAssignmentImage_cut a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier0 order0 params0 first second g p.assignments).symm
  · intro g p
    exact (M.stageTwoTests_image_iff a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 t
      pairing unions powers separation collection carrier1 order1 params1.condition_maps hT
      params1.terms_closed params1.pairs_closed params1.family_ground base directed system1 first second
      g p.assignments p.lower).2 p.tests

end TransitiveGround

end PartitionPilot.Forcing

end OAI
