import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneProjectedFilters

namespace OAI

section

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

local notation "row" => M.stageOneConditionRow a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection

theorem stageOnePairedRowGraph_mem
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    (pres).graph c.pairEmpty row ∈ M.sets := by
  have target := M.stageOneConditionPresentation_carrier_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection nodeOrder omega
  have original := M.stageOneRowGraph_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  rw [M.stageOneRowGraph_eq_graph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection] at original
  have composed := M.relationCompose_mem pairing unions powers separation target carrier pairedCarrier original
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier)
  rw [(pres).relationCompose_graph c c.pairEmpty row id] at composed
  exact composed

theorem stageOneProjectedFilter_codedGeneric
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)), H.GenericFor (M.codedFamily (pres)) →
      (M.stageOneProjectedFilter a c b d T T2 valid pairing unions powers separation carrier order hT
        base directed system collection H).GenericFor (M.codedFamily c.pairEmpty) := by
  let instProjectedFilterSmallOrder := smallOrder
  intro H generic E member dense
  obtain ⟨X, ground, rfl⟩ := member
  have target := M.stageOneConditionPresentation_carrier_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection nodeOrder omega
  have graph := M.stageOnePairedRowGraph_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection nodeOrder omega
  have preimage := M.presentedPreimage_mem (pres) c.pairEmpty row pairing unions powers separation
    target pairedCarrier graph ground
  have densePreimage := M.stageOneSmall_dense_row_preimage a c b d T T2 valid pairing unions powers separation
    carrier order hT base directed system collection dense
  obtain ⟨q, hq, value⟩ := M.generic_meets_coded_dense (pres) H generic preimage densePreimage
  exact ⟨row q,
    (M.stageOneProjectedFilter_row a c b d T T2 valid pairing unions powers separation
      carrier order hT base directed system collection H (row q)).2 ⟨q, hq, rfl⟩, value⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
