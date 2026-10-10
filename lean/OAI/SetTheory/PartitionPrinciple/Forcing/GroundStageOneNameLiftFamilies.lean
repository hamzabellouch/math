import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneGroundAction

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
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
local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "emptyRow" => StageOneCondition.empty M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2

theorem stageOneSmallAction_empty :
    letI := smallOrder
    ∀ (g : G) (p : P), (smallAct).iso g (incl p) = incl (a.iso g p) := by
  let := smallOrder
  intro g p
  apply (equivShrink Condition).symm.injective
  rw [M.stageOneSmallAction_decode a c b d T T2 valid pairing unions powers separation
    carrier order hT indices base directed system collection t inputs hT2 omega]
  change typedAct g ((equivShrink Condition).symm (equivShrink Condition (emptyRow p))) =
    (equivShrink Condition).symm (equivShrink Condition (emptyRow (a.iso g p)))
  rw [(equivShrink Condition).symm_apply_apply, (equivShrink Condition).symm_apply_apply]
  apply StageOneCondition.ext M c.pairEmpty pairing unions powers separation collection
    pairedCarrier pairedOrder hT valid a b d base directed system T2
  · rfl
  · change relationImage ∅ _ _ = ∅
    apply ZFSet.ext
    intro z
    rw [mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, _⟩
      exact (ZFSet.notMem_empty x hx).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim

structure StageOneSmallActionLaws
    (action : letI := smallOrder; PosetAction G (Shrink Condition)) : Prop where
  row : letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      ((equivShrink Condition).symm (action.iso g q)).row =
        a.iso g ((equivShrink Condition).symm q).row
  assignments : letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      ((equivShrink Condition).symm (action.iso g q)).assignments =
        M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g
          ((equivShrink Condition).symm q).assignments
  code : letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (pres).encode (action.iso g q) =
        ZFSet.pair (c.encode (a.iso g ((equivShrink Condition).symm q).row))
          (M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g
            ((equivShrink Condition).symm q).assignments)
  inclusion : letI := smallOrder
    ∀ (g : G) (p : P), action.iso g (incl p) = incl (a.iso g p)

theorem stageOneSmallAction_laws :
    StageOneSmallActionLaws M a c b d T T2 valid pairing unions powers separation carrier order
      nodes hT indices base directed system collection (smallAct) := by
  constructor
  · intro g q
    rw [M.stageOneSmallAction_decode a c b d T T2 valid pairing unions powers separation
      carrier order hT indices base directed system collection t inputs hT2 omega]
    rfl
  · intro g q
    rw [M.stageOneSmallAction_decode a c b d T T2 valid pairing unions powers separation
      carrier order hT indices base directed system collection t inputs hT2 omega]
    rfl
  · exact M.stageOneSmallAction_encode a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega
  · exact M.stageOneSmallAction_empty a c b d T T2 valid pairing unions powers separation
      carrier order hT indices base directed system collection t inputs hT2 omega

end

section
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
variable (collection : CollectionSchema M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "J" => stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T

private theorem flat_coordinates :
    letI := smallOrder
    ∀ (F : FlatConditionSystem M c (pres) J) (q : Shrink Condition),
      F.row q = ((equivShrink Condition).symm q).row ∧
      F.assignments q = ((equivShrink Condition).symm q).assignments := by
  let := smallOrder
  intro F q
  have equal := (F.encode q).symm
  change ZFSet.pair (c.encode (F.row q)) (F.assignments q) =
    ZFSet.pair (c.encode ((equivShrink Condition).symm q).row)
      ((equivShrink Condition).symm q).assignments at equal
  exact ⟨c.injective (ZFSet.pair_inj.1 equal).1, (ZFSet.pair_inj.1 equal).2⟩

theorem stageOneFlatAction_row :
    letI := smallOrder
    ∀ (F : FlatConditionSystem M c (pres) J) (action : PosetAction G (Shrink Condition)),
      StageOneSmallActionLaws M a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection action →
      ∀ (g : G) (q : Shrink Condition), F.row (action.iso g q) = a.iso g (F.row q) := by
  let := smallOrder
  intro F action laws g q
  rw [(flat_coordinates M a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection F (action.iso g q)).1,
    (flat_coordinates M a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection F q).1]
  exact laws.row g q

theorem stageOneFlatAction_assignments :
    letI := smallOrder
    ∀ (F : FlatConditionSystem M c (pres) J) (action : PosetAction G (Shrink Condition)),
      StageOneSmallActionLaws M a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection action →
      ∀ (g : G) (q : Shrink Condition), F.assignments (action.iso g q) =
        M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2 g (F.assignments q) := by
  let := smallOrder
  intro F action laws g q
  rw [(flat_coordinates M a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection F (action.iso g q)).2,
    (flat_coordinates M a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection F q).2]
  exact laws.assignments g q

end

section
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
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "liftName" => M.stageOneNameLift a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

theorem stageOneNameLift_act :
    letI := smallOrder
    ∀ (g : G) (τ : Name c.pairEmpty),
      (smallAct).act (pres) g (liftName τ) = liftName (a.act c.pairEmpty g τ) := by
  let := smallOrder
  intro g τ
  exact a.act_rename_of_equivariant (smallAct) c.pairEmpty (pres) incl
    (fun g p => (M.stageOneSmallAction_empty a c b d T T2 valid pairing unions powers separation
      carrier order hT indices base directed system collection t inputs hT2 omega g p).symm) g τ

theorem stageOneNameLift_stabilizer :
    letI := smallOrder
    ∀ τ : Name c.pairEmpty, (smallAct).stabilizer (pres) (liftName τ) = a.stabilizer c.pairEmpty τ := by
  let := smallOrder
  intro τ
  apply Subgroup.ext
  intro g
  change (smallAct).act (pres) g (liftName τ) = liftName τ ↔ a.act c.pairEmpty g τ = τ
  rw [M.stageOneNameLift_act a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection] using codes
  · intro equal
    exact congrArg liftName equal

theorem stageOneNameLift_supported (K : Subgroup G) (τ : Name c.pairEmpty)
    (supported : K ≤ a.stabilizer c.pairEmpty τ) :
    letI := smallOrder
    K ≤ (smallAct).stabilizer (pres) (liftName τ) := by
  let := smallOrder
  rw [M.stageOneNameLift_stabilizer a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega]
  exact supported

end

section
open SetRealization SetFormula Compression.RecursiveMaps
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
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "liftName" => M.stageOneNameLift a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

theorem stageOneNameLift_hs (F : NormalSubgroupFamily G) (τ : Name c.pairEmpty)
    (hs : HereditarilySymmetric a c.pairEmpty F τ) :
    letI := smallOrder
    HereditarilySymmetric (smallAct) (pres) F (liftName τ) := by
  let := smallOrder
  exact hs.rename (smallAct) (pres) incl
    (fun g p => (M.stageOneSmallAction_empty a c b d T T2 valid pairing unions powers separation
      carrier order hT indices base directed system collection t inputs hT2 omega g p).symm)

theorem stageOneNameFamily_valid (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName c.pairEmpty z) :
    ∀ z ∈ X, IsName (pres) z := by
  intro z hz
  have lifted := (liftName ⟨z, oldValid z hz⟩).property
  exact (congrArg (IsName (pres))
    (M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection ⟨z, oldValid z hz⟩)).mp lifted

theorem stageOneNameFamily_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName c.pairEmpty z) :
    Name.renamedFamily (pres) incl X oldValid = X := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily]
  constructor
  · rintro ⟨τ, hτ, equal⟩
    have codes := M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection τ
    exact (equal.trans codes).symm ▸ hτ
  · intro hz
    exact ⟨⟨z, oldValid z hz⟩, hz,
      (M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection ⟨z, oldValid z hz⟩).symm⟩

theorem stageOneNameFamily_transport (F : NormalSubgroupFamily G) (X : ZFSet.{u})
    (oldValid : ∀ z ∈ X, IsName c.pairEmpty z)
    (closed : ∀ g (τ : Name c.pairEmpty), τ.val ∈ X → (a.act c.pairEmpty g τ).val ∈ X)
    (children : ∀ τ : Name c.pairEmpty, τ.val ∈ X → HereditarilySymmetric a c.pairEmpty F τ) :
    letI := smallOrder
    (∀ z ∈ X, IsName (pres) z) ∧
      (∀ g (τ : Name (pres)), τ.val ∈ X → ((smallAct).act (pres) g τ).val ∈ X) ∧
      (∀ τ : Name (pres), τ.val ∈ X → HereditarilySymmetric (smallAct) (pres) F τ) := by
  let := smallOrder
  refine ⟨M.stageOneNameFamily_valid a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection X oldValid, ?_, ?_⟩
  · intro g τ hτ
    let σ : Name c.pairEmpty := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection σ)
    rw [← same, M.stageOneNameLift_act a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega,
      M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection]
    exact closed g σ hτ
  · intro τ hτ
    let σ : Name c.pairEmpty := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection σ)
    rw [← same]
    exact M.stageOneNameLift_hs a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega F σ (children σ hτ)

end

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
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "liftName" => M.stageOneNameLift a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

theorem stageOneNameAction_val_eq :
    letI := smallOrder
    ∀ (g : G) (τ : Name c.pairEmpty) (σ : Name (pres)), σ.val = τ.val →
      ((smallAct).act (pres) g σ).val = (a.act c.pairEmpty g τ).val := by
  let := smallOrder
  intro g τ σ same
  have lifted : liftName τ = σ := Subtype.ext
    ((M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection τ).trans same.symm)
  rw [← lifted, M.stageOneNameLift_act a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega,
    M.stageOneNameLift_val a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection]

theorem stageOneTermActionGraph_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName c.pairEmpty z)
    (newValid : ∀ z ∈ X, IsName (pres) z) :
    letI := smallOrder
    ∀ g : G, Name.renameFamilyGraph (pres) ((smallAct).iso g) X newValid =
      Name.renameFamilyGraph c.pairEmpty (a.iso g) X oldValid := by
  let := smallOrder
  intro g
  apply ZFSet.ext
  intro z
  rw [Name.mem_renameFamilyGraph, Name.mem_renameFamilyGraph]
  constructor
  · rintro ⟨σ, hs, rfl⟩
    let τ : Name c.pairEmpty := ⟨σ.val, oldValid σ.val hs⟩
    refine ⟨τ, hs, ?_⟩
    have same := M.stageOneNameAction_val_eq a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega g τ σ rfl
    exact congrArg (ZFSet.pair σ.val) same
  · rintro ⟨τ, ht, rfl⟩
    let σ : Name (pres) := ⟨τ.val, newValid τ.val ht⟩
    refine ⟨σ, ht, ?_⟩
    have same := M.stageOneNameAction_val_eq a c b d T T2 valid pairing unions powers separation
      carrier order nodes hT indices base directed system collection t inputs hT2 omega g τ σ rfl
    exact congrArg (ZFSet.pair τ.val) same.symm

theorem stageOneTermActionFamily_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName c.pairEmpty z)
    (newValid : ∀ z ∈ X, IsName (pres) z) :
    letI := smallOrder
    (smallAct).termActionFamily (pres) t X newValid = a.termActionFamily c.pairEmpty t X oldValid := by
  let := smallOrder
  unfold PosetAction.termActionFamily
  congr 1
  funext g
  exact M.stageOneTermActionGraph_eq a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection t inputs hT2 omega X oldValid newValid g

end PartitionPilot.Forcing.TransitiveGround

end OAI
