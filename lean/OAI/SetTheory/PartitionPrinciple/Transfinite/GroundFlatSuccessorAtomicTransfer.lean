import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatSuccessorNameGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
local notation "pi" => M.flatSuccessorSmallRestriction c s I T levels alpha tests F
local notation "projection" => M.flatSuccessorSmallCompleteProjection c s I T levels alpha tests F laws
  pairing unions powers separation infinite choice hLevels hAlpha

include pairing unions powers separation infinite choice hLevels hAlpha

theorem flatSuccessorNameLift_forcesEq :
    letI := smallOrder
    ∀ (q : Shrink Condition) (σ τ : Name s),
      Name.ForcesEq q (liftName σ) (liftName τ) ↔ Name.ForcesEq (pi q) σ τ := by
  let instForcesEqSmallOrder := smallOrder
  intro q σ τ
  exact Name.forcesEq_rename_completeProjection s (pres) pi inc projection q σ τ

theorem flatSuccessorNameLift_forcesMem :
    letI := smallOrder
    ∀ (q : Shrink Condition) (σ τ : Name s),
      Name.ForcesMem q (liftName σ) (liftName τ) ↔ Name.ForcesMem (pi q) σ τ := by
  let instForcesMemSmallOrder := smallOrder
  intro q σ τ
  exact Name.forcesMem_rename_completeProjection s (pres) pi inc projection q σ τ

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
