import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNameGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
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
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
local notation "projection" => M.stageTwoSmallCompleteProjection c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
  infinite choice hI0 hI1
local notation "pi" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F

noncomputable def stageTwoProjectedFilter :
    letI := smallOrder
    ConditionFilter (Shrink Condition) → ConditionFilter P := by
  letI := smallOrder
  exact (projection).projectedFilter

local notation "project" => M.stageTwoProjectedFilter c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
  infinite choice hI0 hI1

theorem stageTwoProjectedFilter_mem_iff :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (p : P),
      (project H).mem p ↔ ∃ q : Shrink Condition, H.mem q ∧ pi q = p := by
  let instProjectedFilterMemSmallOrder := smallOrder
  exact (projection).projectedFilter_mem_iff

theorem stageTwoProjectedFilter_codedGeneric
    (rows : c.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)), H.GenericFor (M.codedFamily (pres)) →
      (project H).GenericFor (M.codedFamily s) := by
  let instProjectedFilterGenericSmallOrder := smallOrder
  intro H generic
  have upperCarrier : (pres).carrier ∈ M.sets :=
    M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid pairing unions powers separation
      rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega
  have graph := M.stageTwoSmallRestriction_graph_mem c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F rows hI0 nodeOrder omega
  exact M.completeProjection_codedGeneric (pres) s (projection)
    pairing unions powers separation upperCarrier carrier graph H generic

theorem stageTwoProjectedFilter_eval :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (tau : Name s),
      Name.eval H.mem (M.stageTwoNameLift c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order nodes hT indices
        base directed system F first second tau) = Name.eval (project H).mem tau := by
  let instProjectedFilterEvalSmallOrder := smallOrder
  intro H tau
  exact M.stageTwoNameLift_eval c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices
    base directed system F first second H.mem tau

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
