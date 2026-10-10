import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatSuccessorNameGraphs
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageThreeAssignmentFamilies

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u v
variable {G : Type v} {R P : Type u} [Group G]
variable [PartialOrder R] [PartialOrder P]

structure FlatSuccessorActionInputs (M : TransitiveGround.{u})
    (c : Presentation R) (s : Presentation P)
    (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
    (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
    (image : G → ZFSet.{u} → ZFSet.{u}) : Prop where
  small : ∀ g A, A ∈ M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega →
    image g A ∈ M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
  one : ∀ A, A ⊆ stageOneAssignments I T → image 1 A = A
  mul : ∀ g h A, A ⊆ stageOneAssignments I T →
    image (g * h) A = image g (image h A)
  mono : ∀ g A B, A ⊆ B → image g A ⊆ image g B
  lower_code : ∀ g (p : FlatSuccessorCondition M c s I T levels alpha tests),
    s.encode (lowerAction.iso g p.lower) = ZFSet.pair (c.encode (rowAction.iso g p.row))
      (assignmentCut levels alpha (image g p.assignments))
  tests : ∀ g (p : FlatSuccessorCondition M c s I T levels alpha tests),
    tests (image g p.assignments) (lowerAction.iso g p.lower)

end

section
open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u}) {G : Type v} {R P : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "J" => stageOneAssignments I T

noncomputable def act (g : G) (p : Condition) : Condition where
  row := rowAction.iso g p.row
  assignments := image g p.assignments
  assignments_mem := inputs.small g p.assignments p.assignments_mem
  lower := lowerAction.iso g p.lower
  lower_code := inputs.lower_code g p
  tests := inputs.tests g p

local notation "act'" => act M c s I T levels alpha tests rowAction lowerAction image inputs

theorem act_fields (g : G) (p : Condition) :
    (act' g p).row = rowAction.iso g p.row ∧
      (act' g p).assignments = image g p.assignments ∧ (act' g p).lower = lowerAction.iso g p.lower :=
  ⟨rfl, rfl, rfl⟩

theorem act_one (p : Condition) : act' 1 p = p := by
  apply ext M c s I T levels alpha tests
  · exact rowAction.one p.row
  · exact inputs.one p.assignments ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).1 p.assignments_mem).2.1

theorem act_mul (g h : G) (p : Condition) : act' (g * h) p = act' g (act' h p) := by
  apply ext M c s I T levels alpha tests
  · exact rowAction.mul g h p.row
  · exact inputs.mul g h p.assignments ((M.mem_groundSmallSubsets J ZFSet.omega p.assignments).1 p.assignments_mem).2.1

theorem act_inv_left (g : G) (p : Condition) : act' g⁻¹ (act' g p) = p := by
  rw [← act_mul M c s I T levels alpha tests rowAction lowerAction image inputs, inv_mul_cancel, act_one]

theorem act_inv_right (g : G) (p : Condition) : act' g (act' g⁻¹ p) = p := by
  rw [← act_mul M c s I T levels alpha tests rowAction lowerAction image inputs, mul_inv_cancel, act_one]

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
  left_inv := act_inv_left M c s I T levels alpha tests rowAction lowerAction image inputs g
  right_inv := act_inv_right M c s I T levels alpha tests rowAction lowerAction image inputs g
  map_rel_iff' := act_le_iff M c s I T levels alpha tests rowAction lowerAction image inputs g _ _

noncomputable def posetAction : PosetAction G Condition where
  iso := actOrderIso M c s I T levels alpha tests rowAction lowerAction image inputs
  one := act_one M c s I T levels alpha tests rowAction lowerAction image inputs
  mul := act_mul M c s I T levels alpha tests rowAction lowerAction image inputs

end FlatSuccessorCondition

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "act'" => act M c s I T levels alpha tests rowAction lowerAction image inputs

theorem act_eq_iff (g : G) (p : Condition) :
    act' g p = p ↔ rowAction.iso g p.row = p.row ∧ image g p.assignments = p.assignments := by
  constructor
  · intro same
    exact ⟨congrArg (fun q : Condition => q.row) same,
      congrArg (fun q : Condition => q.assignments) same⟩
  · rintro ⟨row, assignments⟩
    exact ext M c s I T levels alpha tests row assignments

end FlatSuccessorCondition
end

namespace TransitiveGround
open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u}) {G : Type v} {R P : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
local notation "typedAct" => FlatSuccessorCondition.act M c s I T levels alpha tests rowAction lowerAction image inputs

noncomputable def flatSuccessorSmallAction :
    letI := smallOrder
    PosetAction G (Shrink Condition) := by
  letI := smallOrder
  let original := FlatSuccessorCondition.posetAction M c s I T levels alpha tests rowAction lowerAction image inputs
  let e := M.flatSuccessorOrderIso c s I T levels alpha tests
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

local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs

theorem flatSuccessorSmallAction_decode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (equivShrink Condition).symm ((smallAct).iso g q) =
        typedAct g ((equivShrink Condition).symm q) := by
  let := smallOrder
  intro g q
  change (equivShrink Condition).symm
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact (equivShrink Condition).symm_apply_apply _

theorem flatSuccessorSmallAction_encode :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (pres).encode ((smallAct).iso g q) =
        ZFSet.pair (c.encode (rowAction.iso g ((equivShrink Condition).symm q).row))
          (image g ((equivShrink Condition).symm q).assignments) := by
  let := smallOrder
  intro g q
  change (pres).encode
    (equivShrink Condition (typedAct g ((equivShrink Condition).symm q))) = _
  exact M.flatSuccessorPresentation_encode c s I T levels alpha tests _

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests
  rowAction lowerAction image inputs
variable (t : Presentation G) (assignmentGraph : G → ZFSet.{u})
variable (image_eq : ∀ g A, image g A = relationImage A (stageOneAssignments I T) (assignmentGraph g))
local notation "fullGraph" => M.flatSuccessorFullActionGraph c s I T levels alpha tests
  rowAction t assignmentGraph
include image_eq

theorem flatSuccessorSmallActionGraph_eq :
    letI := smallOrder
    (smallAct).actionGraph (pres) t = fullGraph := by
  let := smallOrder
  have encoded (g : G) (x : Shrink Condition) := M.flatSuccessorSmallAction_encode c s I T levels alpha tests rowAction lowerAction image inputs g x
  have meaning (g : G) (x y : Shrink Condition) :
      ZFSet.pair (ZFSet.pair (t.encode g) ((pres).encode x)) ((pres).encode y) ∈ fullGraph ↔
      (smallAct).iso g x = y := by
    change ZFSet.pair (ZFSet.pair (t.encode g)
      (ZFSet.pair (c.encode ((equivShrink Condition).symm x).row)
        ((equivShrink Condition).symm x).assignments))
      (ZFSet.pair (c.encode ((equivShrink Condition).symm y).row)
        ((equivShrink Condition).symm y).assignments) ∈ fullGraph ↔ _
    rw [M.flatSuccessorFullActionGraph_entry, ← image_eq g]
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
    unfold flatSuccessorFullActionGraph rowAssignmentActionGraph at boundMember
    have bounds : z ∈ ZFSet.prod (ZFSet.prod t.carrier (pres).carrier) (pres).carrier :=
      (ZFSet.mem_sep.1 boundMember).1
    obtain ⟨source,hSource,y,hy,rfl⟩ := ZFSet.mem_prod.1 bounds
    obtain ⟨g,hg,x,hx,rfl⟩ := ZFSet.mem_prod.1 hSource
    obtain ⟨g,rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x,rfl⟩ := ((pres).mem_carrier x).1 hx
    obtain ⟨y,rfl⟩ := ((pres).mem_carrier y).1 hy
    exact ((smallAct).triple_mem_actionGraph (pres) t g x y).2 ((meaning g x y).1 member)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (rows : c.carrier ∈ M.sets)
variable (conditions : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets)
variable (assignments : stageOneAssignments I T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (rowMaps : rowAction.conditionMapFamily c t ∈ M.sets)
variable (assignmentMaps : familyCodeGraph t.encode assignmentGraph ∈ M.sets)
include pairing unions powers separation rows conditions assignments omega group rowMaps assignmentMaps

theorem flatSuccessorSmallActionGraph_mem :
    letI := smallOrder
    (smallAct).actionGraph (pres) t ∈ M.sets := by
  let := smallOrder
  rw [M.flatSuccessorSmallActionGraph_eq c s I T levels alpha tests
    rowAction lowerAction image inputs t assignmentGraph image_eq]
  exact M.flatSuccessorFullActionGraph_mem c s I T levels alpha tests rowAction t assignmentGraph
    pairing unions powers separation rows conditions assignments omega group rowMaps assignmentMaps

theorem flatSuccessorSmallActionMapFamily_mem (collection : CollectionSchema M.sets) :
    letI := smallOrder
    (smallAct).conditionMapFamily (pres) t ∈ M.sets := by
  let := smallOrder
  exact M.conditionMapFamily_mem_of_actionGraph (smallAct) (pres) t
    pairing unions powers separation collection conditions group
    (M.flatSuccessorSmallActionGraph_mem c s I T levels alpha tests
      rowAction lowerAction image inputs t assignmentGraph image_eq
      pairing unions powers separation rows conditions assignments omega group rowMaps assignmentMaps)

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u}) {G : Type v} {R P : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs

theorem flatSuccessorSmallAction_fixed_iff :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (smallAct).iso g q = q ↔
      rowAction.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row ∧
      image g ((equivShrink Condition).symm q).assignments = ((equivShrink Condition).symm q).assignments := by
  let := smallOrder
  intro g q
  have decoded := M.flatSuccessorSmallAction_decode c s I T levels alpha tests
    rowAction lowerAction image inputs g q
  have typed := FlatSuccessorCondition.act_eq_iff M c s I T levels alpha tests
    rowAction lowerAction image inputs g ((equivShrink Condition).symm q)
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
universe u v
variable (M : TransitiveGround.{u}) {G : Type v} {R P : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
local notation "smallRestrict" => M.flatSuccessorSmallRestriction c s I T levels alpha tests F
local notation "smallInc" => M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws

theorem flatSuccessorSmallRestriction_equivariant :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      smallRestrict ((smallAct).iso g q) = lowerAction.iso g (smallRestrict q) := by
  let := smallOrder
  intro g q
  change ((equivShrink Condition).symm ((smallAct).iso g q)).lower =
    lowerAction.iso g ((equivShrink Condition).symm q).lower
  rw [M.flatSuccessorSmallAction_decode]
  rfl

theorem flatSuccessorSmallInclusion_equivariant :
    letI := smallOrder
    ∀ (g : G) (p : P),
      (smallAct).iso g (smallInc p) = smallInc (lowerAction.iso g p) := by
  let := smallOrder
  have retract (p : P) : smallRestrict (smallInc p) = p := by
    change ((equivShrink Condition).symm
      (equivShrink Condition (FlatSuccessorCondition.inclusion M c s I T levels alpha tests F laws p))).lower = p
    rw [Equiv.symm_apply_apply]
    rfl
  have le_include (q : Shrink Condition) (p : P) :
      q ≤ smallInc p ↔ smallRestrict q ≤ p := by
    change (equivShrink Condition).symm q ≤
      (equivShrink Condition).symm (equivShrink Condition
        (FlatSuccessorCondition.inclusion M c s I T levels alpha tests F laws p)) ↔ _
    rw [Equiv.symm_apply_apply]
    exact FlatSuccessorCondition.le_inclusion_iff M c s I T levels alpha tests F laws _ p
  have forward (h : G) (p : P) :
      (smallAct).iso h (smallInc p) ≤ smallInc (lowerAction.iso h p) := by
    apply (le_include _ _).2
    rw [M.flatSuccessorSmallRestriction_equivariant, retract]
  intro g p
  apply le_antisymm (forward g p)
  have back := ((smallAct).iso g).monotone (forward g⁻¹ (lowerAction.iso g p))
  have cancel : lowerAction.iso g⁻¹ (lowerAction.iso g p) = p := by
    rw [← lowerAction.mul, inv_mul_cancel, lowerAction.one]
  rw [cancel, ← (smallAct).mul, mul_inv_cancel, (smallAct).one] at back
  exact back

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
local notation "inc" => M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws
local notation "liftName" => M.flatSuccessorNameLift c s I T levels alpha tests F laws
variable {G : Type v} [Group G]
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs

theorem flatSuccessorNameLift_act :
    letI := smallOrder
    ∀ (g : G) (τ : Name s),
      (smallAct).act (pres) g (liftName τ) = liftName (lowerAction.act s g τ) := by
  let := smallOrder
  intro g τ
  exact lowerAction.act_rename_of_equivariant (smallAct) s (pres) inc
    (fun g p => (M.flatSuccessorSmallInclusion_equivariant c s I T levels alpha tests rowAction lowerAction image inputs F laws g p).symm) g τ

theorem flatSuccessorNameLift_stabilizer :
    letI := smallOrder
    ∀ τ : Name s, (smallAct).stabilizer (pres) (liftName τ) = lowerAction.stabilizer s τ := by
  let := smallOrder
  intro τ
  apply Subgroup.ext
  intro g
  change (smallAct).act (pres) g (liftName τ) = liftName τ ↔ lowerAction.act s g τ = τ
  rw [M.flatSuccessorNameLift_act c s I T levels alpha tests F laws rowAction lowerAction image inputs]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.flatSuccessorNameLift_val c s I T levels alpha tests F laws] using codes
  · intro equal
    exact congrArg liftName equal

theorem flatSuccessorNameLift_supported (K : Subgroup G) (τ : Name s)
    (supported : K ≤ lowerAction.stabilizer s τ) :
    letI := smallOrder
    K ≤ (smallAct).stabilizer (pres) (liftName τ) := by
  let := smallOrder
  rw [M.flatSuccessorNameLift_stabilizer c s I T levels alpha tests F laws rowAction lowerAction image inputs]
  exact supported

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P P2 L : Type u}
variable [Group G] [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder P2] [OrderTop P2] [PartialOrder L]
variable (a0 : PosetAction G R) (s0 c : Presentation R)
variable (a1 : PosetAction G P) (s1 : Presentation P)
variable (a2 : PosetAction G P2) (s2 : Presentation P2)
variable (b : Presentation L) (d : PosetAction G L) (T T2 : ZFSet.{u})
variable (v0 : ∀ z ∈ T, IsName s0 z) (v02 : ∀ z ∈ T2, IsName s0 z)
variable (v1 : ∀ z ∈ T, IsName s1 z) (v12 : ∀ z ∈ T2, IsName s1 z)
variable (v2 : ∀ z ∈ T, IsName s2 z) (v22 : ∀ z ∈ T2, IsName s2 z)
local notation "I0" => M.niceRefinementIndices a0 s0 b d ∅ T T2 v0
local notation "I1" => M.niceRefinementIndices a1 s1 b d (natSetCode 1) T T2 v1
local notation "I2" => M.niceRefinementIndices a2 s2 b d (natSetCode 2) T T2 v2
local notation "image" => M.stageThreeAssignmentImage a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T

theorem stageThreeActionInputs
    (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier0 : s0.carrier ∈ M.sets) (order0 : s0.conditionOrder ∈ M.sets)
    (carrier1 : s1.carrier ∈ M.sets) (order1 : s1.conditionOrder ∈ M.sets)
    (carrier2 : s2.carrier ∈ M.sets) (order2 : s2.conditionOrder ∈ M.sets)
    (params0 : StageOneActionParameters M a0 s0 t b d T T2 v0)
    (params1 : StageOneActionParameters M a1 s1 t b d T T2 v1)
    (params2 : StageOneActionParameters M a2 s2 t b d T T2 v2)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hI2 : I2 ∈ M.sets)
    (first : RefinementIndexLevelCode I0 ∅) (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2))
    (omega : ZFSet.omega ∈ M.sets)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system2 : NiceNameSystem M a2 s2 b d base directed T v2)
    (F : FlatConditionSystem M c s2 (stageOneAssignments (I0 ∪ I1) T))
    (row_equivariant : ∀ g q, F.row (a2.iso g q) = a0.iso g (F.row q))
    (data_equivariant : ∀ g q, F.assignments (a2.iso g q) =
      M.stageTwoAssignmentImage a0 s0 a1 s1 b d T T2 v0 v02 v1 v12 g (F.assignments q)) :
    FlatSuccessorActionInputs M c s2 ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2)
      (M.refinementLevelTests s2 pairing unions powers separation collection carrier2 order2 hT v2
        a2 b d base directed system2 (natSetCode 2) T2) a0 a2 image := by
  let tests := M.refinementLevelTests s2 pairing unions powers separation collection carrier2 order2 hT v2
    a2 b d base directed system2 (natSetCode 2) T2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g A member
    exact M.stageThreeAssignmentImage_small a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
      params0 params1 params2 first second third hT hT2 hI0 hI1 hI2 omega g member
  · intro A subset
    exact M.stageThreeAssignmentImage_one a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
      params0 params1 params2 first second third subset
  · intro g h A subset
    exact M.stageThreeAssignmentImage_mul a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier0 order0 carrier1 order1 carrier2 order2
      params0 params1 params2 first second third g h subset
  · intro g A B subset
    exact M.stageThreeAssignmentImage_mono a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 g subset
  · intro g p
    rw [F.encode, row_equivariant, data_equivariant,
      FlatSuccessorCondition.lower_row M c s2 ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F p,
      FlatSuccessorCondition.lower_assignments M c s2 ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F p]
    exact congrArg (ZFSet.pair (c.encode (a0.iso g p.row)))
      (M.stageThreeAssignmentImage_cut a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
        pairing unions powers separation collection carrier0 order0 carrier1 order1
        params0 params1 first second third g p.assignments).symm
  · intro g p
    exact (M.stageThreeTests_image_iff a0 s0 a1 s1 a2 s2 b d T T2 v0 v02 v1 v12 v2 v22 t
      pairing unions powers separation collection carrier2 order2 params2.condition_maps hT
      params2.terms_closed params2.pairs_closed params2.family_ground base directed system2 first second third
      g p.assignments p.lower).2 p.tests

end TransitiveGround

end PartitionPilot.Forcing

end OAI
