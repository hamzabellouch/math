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

local notation "restrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
include infinite choice hI0 hI1

theorem stageTwoNameLift_forcesEq :
    letI := smallOrder
    ∀ (q : Shrink Condition) (σ τ : Name s),
      Name.ForcesEq q (liftName σ) (liftName τ) ↔ Name.ForcesEq (restrict q) σ τ := by
  let := smallOrder
  intro q σ τ
  exact Name.forcesEq_rename_completeProjection s (pres) restrict inc
    (M.stageTwoSmallCompleteProjection c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system F first second
      infinite choice hI0 hI1) q σ τ

theorem stageTwoNameLift_forcesMem :
    letI := smallOrder
    ∀ (q : Shrink Condition) (σ τ : Name s),
      Name.ForcesMem q (liftName σ) (liftName τ) ↔ Name.ForcesMem (restrict q) σ τ := by
  let := smallOrder
  intro q σ τ
  exact Name.forcesMem_rename_completeProjection s (pres) restrict inc
    (M.stageTwoSmallCompleteProjection c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system F first second
      infinite choice hI0 hI1) q σ τ

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
