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

noncomputable def flatSuccessorProjectedFilter :
    letI := smallOrder
    ConditionFilter (Shrink Condition) → ConditionFilter P := by
  letI := smallOrder
  exact (projection).projectedFilter

local notation "project" => M.flatSuccessorProjectedFilter c s I T levels alpha tests F laws
  pairing unions powers separation infinite choice hLevels hAlpha

theorem flatSuccessorProjectedFilter_mem_iff :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (p : P),
      (project H).mem p ↔ ∃ q : Shrink Condition, H.mem q ∧ pi q = p := by
  let := smallOrder
  exact (projection).projectedFilter_mem_iff

theorem flatSuccessorProjectedFilter_codedGeneric
    (lower : s.carrier ∈ M.sets)
    (upper : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets) :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)), H.GenericFor (M.codedFamily (pres)) →
      (project H).GenericFor (M.codedFamily s) := by
  let := smallOrder
  intro H generic
  have graph := M.presentedRowAssignmentCutGraph_mem pairing unions powers separation
    pres s pi (fun p => c.encode ((equivShrink Condition).symm p).row)
    (fun p => ((equivShrink Condition).symm p).assignments) levels alpha
    (fun _ => rfl) (M.flatSuccessorSmallRestriction_encode c s I T levels alpha tests F)
    upper lower hLevels hAlpha
  exact M.completeProjection_codedGeneric (pres) s (projection)
    pairing unions powers separation upper lower graph H generic

theorem flatSuccessorProjectedFilter_eval :
    letI := smallOrder
    ∀ (H : ConditionFilter (Shrink Condition)) (tau : Name s),
      Name.eval H.mem (liftName tau) = Name.eval (project H).mem tau := by
  let := smallOrder
  intro H tau
  exact M.flatSuccessorNameLift_eval c s I T levels alpha tests F laws H.mem tau

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
