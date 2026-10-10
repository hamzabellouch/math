import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneFlatConditions

namespace OAI

section

namespace PartitionPilot.Forcing
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

namespace StageOneCondition
variable {M s pairing unions powers separation collection carrier order hT valid a b d base directed system T2}
local notation "Condition" => StageOneCondition M s pairing unions powers separation collection
  carrier order hT valid a b d base directed system T2

local notation "emptyRow" => empty M s pairing unions powers separation collection carrier order hT valid
  a b d base directed system T2

theorem le_empty_iff (q : Condition) (p : P) : q ≤ emptyRow p ↔ q.row ≤ p := by
  exact ⟨fun below => below.1, fun below => ⟨below, ZFSet.empty_subset _⟩⟩

theorem compatible_empty_iff (q : Condition) (p : P) :
    Compatible q (emptyRow p) ↔ Compatible q.row p := by
  constructor
  · rintro ⟨r, below, included⟩
    exact ⟨r.row, below.1, included.1⟩
  · rintro ⟨row, below, included⟩
    exact ⟨q.withRow row below, q.withRow_le row below, (le_empty_iff _ p).2 included⟩

theorem dense_row_preimage {E : Set P} (dense : Dense E) :
    Dense {q : Condition | q.row ∈ E} := by
  intro q
  obtain ⟨row, below, member⟩ := dense q.row
  exact ⟨q.withRow row below, q.withRow_le row below, member⟩

noncomputable def rowFilter (H : ConditionFilter Condition) : ConditionFilter P where
  mem p := H.mem (emptyRow p)
  nonempty := by
    obtain ⟨q, member⟩ := H.nonempty
    exact ⟨q.row, H.upward member ((le_empty_iff q q.row).2 le_rfl)⟩
  upward := by
    intro p q member below
    exact H.upward member ⟨below, fun _ h => h⟩
  directed := by
    intro p q hp hq
    obtain ⟨r, member, rp, rq⟩ := H.directed hp hq
    exact ⟨r.row, H.upward member ((le_empty_iff r r.row).2 le_rfl), rp.1, rq.1⟩

theorem rowFilter_mem_iff (H : ConditionFilter Condition) (p : P) :
    (rowFilter H).mem p ↔ ∃ q : Condition, H.mem q ∧ q.row = p := by
  constructor
  · intro member
    exact ⟨emptyRow p, member, rfl⟩
  · rintro ⟨q, member, rfl⟩
    exact H.upward member ((le_empty_iff q q.row).2 le_rfl)

theorem rowFilter_meets_iff (H : ConditionFilter Condition) (E : Set P) :
    (rowFilter H).Meets E ↔ H.Meets {q : Condition | q.row ∈ E} := by
  constructor
  · rintro ⟨p, member, hp⟩
    obtain ⟨q, hq, rfl⟩ := (rowFilter_mem_iff H p).1 member
    exact ⟨q, hq, hp⟩
  · rintro ⟨q, member, hp⟩
    exact ⟨q.row, (rowFilter_mem_iff H q.row).2 ⟨q, member, rfl⟩, hp⟩

theorem rowFilter_generic (H : ConditionFilter Condition) (family : Set (Set P))
    (generic : H.GenericFor ((fun E : Set P => {q : Condition | q.row ∈ E}) '' family)) :
    (rowFilter H).GenericFor family := by
  intro E member dense
  exact (rowFilter_meets_iff H E).2
    (generic _ ⟨E, member, rfl⟩ (dense_row_preimage dense))

end StageOneCondition
end PartitionPilot.Forcing



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

local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection
local notation "emptyRow" => StageOneCondition.empty M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2

local notation "incl" => M.stageOneEmptyInclusion a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection

noncomputable def stageOneProjectedFilter
    (H : @ConditionFilter (Shrink Condition) (smallOrder).toPreorder) : ConditionFilter P := by
  let := smallOrder
  let e := M.stageOneConditionOrderIso a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection
  let F : ConditionFilter Condition := {
    mem p := H.mem (e p)
    nonempty := by
      obtain ⟨q, hq⟩ := H.nonempty
      exact ⟨e.symm q, by simpa only [OrderIso.apply_symm_apply] using hq⟩
    upward := by
      intro p q member below
      exact H.upward member (e.monotone below)
    directed := by
      intro p q hp hq
      obtain ⟨r, hr, rp, rq⟩ := H.directed hp hq
      exact ⟨e.symm r, by simpa only [OrderIso.apply_symm_apply] using hr,
        (e.symm.monotone rp).trans_eq (e.symm_apply_apply p),
        (e.symm.monotone rq).trans_eq (e.symm_apply_apply q)⟩ }
  exact StageOneCondition.rowFilter F

theorem stageOneProjectedFilter_mem :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (p : P),
    (M.stageOneProjectedFilter a c b d T T2 valid pairing unions powers separation carrier order hT
      base directed system collection H).mem p ↔ H.mem (incl p) := by
  let := smallOrder
  intro H p
  rfl

theorem stageOneProjectedFilter_row :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (p : P),
    (M.stageOneProjectedFilter a c b d T T2 valid pairing unions powers separation carrier order hT
      base directed system collection H).mem p ↔
      ∃ q : Shrink Condition, H.mem q ∧ ((equivShrink Condition).symm q).row = p := by
  let := smallOrder
  intro H p
  constructor
  · intro member
    refine ⟨incl p, member, ?_⟩
    change ((equivShrink Condition).symm (equivShrink Condition (emptyRow p))).row = p
    rw [Equiv.symm_apply_apply]
    rfl
  · rintro ⟨q, member, rfl⟩
    apply H.upward member
    change (equivShrink Condition).symm q ≤
      (equivShrink Condition).symm (equivShrink Condition (emptyRow ((equivShrink Condition).symm q).row))
    rw [Equiv.symm_apply_apply]
    exact (StageOneCondition.le_empty_iff _ _).2 le_rfl

theorem stageOneSmall_dense_row_preimage {E : Set P} (dense : Dense E) :
    letI := smallOrder
    Dense {q : Shrink Condition | ((equivShrink Condition).symm q).row ∈ E} := by
  let := smallOrder
  intro q
  let q' := (equivShrink Condition).symm q
  obtain ⟨row, below, member⟩ := dense q'.row
  refine ⟨equivShrink Condition (q'.withRow row below), ?_, ?_⟩
  · change (equivShrink Condition).symm (equivShrink Condition (q'.withRow row below)) ≤ q'
    rw [Equiv.symm_apply_apply]
    exact q'.withRow_le row below
  · change ((equivShrink Condition).symm (equivShrink Condition (q'.withRow row below))).row ∈ E
    rw [Equiv.symm_apply_apply]
    exact member

theorem stageOneProjectedFilter_generic :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (family : Set (Set P)),
    H.GenericFor
      ((fun E : Set P => {q : Shrink Condition | ((equivShrink Condition).symm q).row ∈ E}) '' family) →
    (M.stageOneProjectedFilter a c b d T T2 valid pairing unions powers separation carrier order hT
      base directed system collection H).GenericFor family := by
  let := smallOrder
  intro H family generic E hE dense
  obtain ⟨q, hq, member⟩ := generic _ ⟨E, hE, rfl⟩
    (M.stageOneSmall_dense_row_preimage a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection dense)
  exact ⟨((equivShrink Condition).symm q).row,
    (M.stageOneProjectedFilter_row a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection H _).2 ⟨q, hq, rfl⟩, member⟩

theorem stageOneNameLift_projected_eval :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (tau : Name c.pairEmpty),
    Name.eval H.mem (M.stageOneNameLift a c b d T T2 valid pairing unions powers separation carrier order nodes hT
      indices base directed system collection tau) =
      Name.eval (M.stageOneProjectedFilter a c b d T T2 valid pairing unions powers separation carrier order hT
        base directed system collection H).mem tau := by
  let := smallOrder
  intro H tau
  exact M.stageOneNameLift_eval a c b d T T2 valid pairing unions powers separation carrier order nodes hT
    indices base directed system collection H.mem tau

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
