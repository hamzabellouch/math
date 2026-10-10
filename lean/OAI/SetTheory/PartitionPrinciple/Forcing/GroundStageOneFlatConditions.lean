import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneSequenceProjections

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)

noncomputable def stageOneForcingOrder : ZFSet.{u} :=
  rowAssignmentOrder (M.stageOneForcing a c b d T T2 valid) c.carrier
    (M.groundSmallSubsets
      (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) ZFSet.omega)
    c.conditionOrder

theorem stageOneForcingOrder_entry (q p : P) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (c.encode q) A) (ZFSet.pair (c.encode p) D) ∈
        M.stageOneForcingOrder a c b d T T2 valid ↔
      ZFSet.pair (c.encode q) A ∈ M.stageOneForcing a c b d T T2 valid ∧
      ZFSet.pair (c.encode p) D ∈ M.stageOneForcing a c b d T T2 valid ∧ q ≤ p ∧ D ⊆ A := by
  rw [stageOneForcingOrder, pair_mem_rowAssignmentOrder]
  constructor
  · rintro ⟨hq,hp,_,_,_,_,rows,subset⟩
    exact ⟨hq,hp,(c.pair_mem_conditionOrder q p).1 rows,subset⟩
  · rintro ⟨hq,hp,rows,subset⟩
    have qFields := (M.pair_mem_stageOneConditions c.carrier _ (c.encode q) A).1 hq
    have pFields := (M.pair_mem_stageOneConditions c.carrier _ (c.encode p) D).1 hp
    exact ⟨hq,hp,c.encode_mem q,
      (M.mem_groundSmallSubsets _ _ A).2 ⟨qFields.2.1,qFields.2.2.1,qFields.2.2.2.1⟩,
      c.encode_mem p,
      (M.mem_groundSmallSubsets _ _ D).2 ⟨pFields.2.1,pFields.2.2.1,pFields.2.2.2.1⟩,
      (c.pair_mem_conditionOrder q p).2 rows,subset⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)

include pairing unions powers separation carrier order nodes hT indices system in
theorem stageOneForcingOrder_mem (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneForcingOrder a c b d T T2 valid ∈ M.sets := by
  have conditions := M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT
  have small := M.groundSmallSubsets_mem powers separation assignments omega
  exact M.rowAssignmentOrder_mem pairing unions powers separation conditions carrier small order

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
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
local notation "Q" => M.stageOneForcing a c b d T T2 valid

@[instance_reducible]
noncomputable def stageOneConditionSmallOrder : PartialOrder (Shrink Condition) where
  le p q := (equivShrink Condition).symm p ≤ (equivShrink Condition).symm q
  le_refl _ := le_rfl
  le_trans _ _ _ first second := first.trans second
  le_antisymm _ _ first second := (equivShrink Condition).symm.injective (le_antisymm first second)

noncomputable def stageOneConditionOrderIso :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
    Condition ≃o Shrink Condition := by
  letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
  exact {
    toEquiv := equivShrink Condition
    map_rel_iff' := by
      intro p q
      change (equivShrink Condition).symm (equivShrink Condition p) ≤
        (equivShrink Condition).symm (equivShrink Condition q) ↔ p ≤ q
      simp only [Equiv.symm_apply_apply] }

@[instance_reducible]
noncomputable def stageOneConditionSmallTop :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
    OrderTop (Shrink Condition) := by
  letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
  exact {
    top := equivShrink Condition ⊤
    le_top p := by
      change (equivShrink Condition).symm p ≤ (equivShrink Condition).symm (equivShrink Condition ⊤)
      rw [Equiv.symm_apply_apply]
      exact le_top }

local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

theorem stageOneConditionOrder_graph :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
    (pres).conditionOrder = M.stageOneForcingOrder a c b d T T2 valid := by
  let := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
  apply ZFSet.ext
  intro z
  rw [Presentation.conditionOrder, Presentation.mem_subset]
  constructor
  · rintro ⟨⟨q,p⟩, below, rfl⟩
    let q' := (equivShrink Condition).symm q
    let p' := (equivShrink Condition).symm p
    exact (M.stageOneForcingOrder_entry a c b d T T2 valid q'.row p'.row q'.assignments p'.assignments).2
      ⟨(pres).encode_mem q, (pres).encode_mem p, below.1, below.2⟩
  · intro member
    have bound := (mem_rowAssignmentOrder _ _ _ _ z).1 member
    obtain ⟨rawQ, hq, rawP, hp, equal⟩ := ZFSet.mem_prod.1 bound.1
    obtain ⟨q, eqQ⟩ := ((pres).mem_carrier rawQ).1 hq
    obtain ⟨p, eqP⟩ := ((pres).mem_carrier rawP).1 hp
    have entries : ZFSet.pair ((pres).encode q) ((pres).encode p) ∈
        M.stageOneForcingOrder a c b d T T2 valid := by
      rw [eqQ, eqP, ← equal]
      exact member
    let q' := (equivShrink Condition).symm q
    let p' := (equivShrink Condition).symm p
    have parts := (M.stageOneForcingOrder_entry a c b d T T2 valid
      q'.row p'.row q'.assignments p'.assignments).1 entries
    refine ⟨(q,p), ⟨parts.2.2.1, parts.2.2.2⟩, ?_⟩
    change ZFSet.pair ((pres).encode q) ((pres).encode p) = z
    rw [eqQ, eqP]
    exact equal.symm

theorem stageOneConditionOrder_mem
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
    (pres).conditionOrder ∈ M.sets := by
  let := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation carrier order hT base directed system collection
  rw [M.stageOneConditionOrder_graph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection]
  exact M.stageOneForcingOrder_mem a c b d T T2 valid pairing unions powers separation carrier order nodes hT
    indices base directed system nodeOrder omega

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
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
local notation "Q" => M.stageOneForcing a c b d T T2 valid

noncomputable def stageOneFlatConditionSystem :
    letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection
    FlatConditionSystem M c
      (M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
        carrier order nodes hT indices base directed system collection)
      (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) := by
  letI := M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection
  exact {
    row := M.stageOneConditionRow a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection
    assignments := fun q => ((equivShrink Condition).symm q).assignments
    encode := fun _ => rfl
    le_iff := fun _ _ => Iff.rfl
    assignments_mem := fun q => ((equivShrink Condition).symm q).assignments_mem }

end PartitionPilot.Forcing.TransitiveGround

end OAI
