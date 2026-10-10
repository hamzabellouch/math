import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageThreeSuccessorLaws

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

noncomputable def flatSuccessorNameLift (tau : Name s) : Name (pres) := by
  let := smallOrder
  exact Name.rename (pres) inc tau

local notation "liftName" => M.flatSuccessorNameLift c s I T levels alpha tests F laws

theorem flatSuccessorNameLift_val (tau : Name s) : (liftName tau).val = tau.val := by
  let := smallOrder
  exact Name.rename_val_of_encode (pres) inc
    (M.flatSuccessorSmallInclusion_encode c s I T levels alpha tests F laws) tau

theorem flatSuccessorNameLift_mem (tau : Name s) (ground : tau.val ∈ M.sets) :
    (liftName tau).val ∈ M.sets := by
  rw [M.flatSuccessorNameLift_val]
  exact ground

theorem flatSuccessorNameLift_eval :
    letI := smallOrder
    ∀ (H : Set (Shrink Condition)) (tau : Name s),
      Name.eval H (liftName tau) = Name.eval {p | inc p ∈ H} tau := by
  let := smallOrder
  intro H tau
  exact Name.eval_rename (pres) inc H tau

end PartitionPilot.Forcing.TransitiveGround



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
variable (carrier : s.carrier ∈ M.sets)

theorem flatSuccessorSmallInclusion_graph :
    letI := smallOrder
    s.graph (pres) inc = identityFunctionGraph s.carrier := by
  let := smallOrder
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨p, rfl⟩
    rw [M.flatSuccessorSmallInclusion_encode]
    exact ⟨s.encode p, s.encode_mem p, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, congrArg (ZFSet.pair (s.encode p))
      (M.flatSuccessorSmallInclusion_encode c s I T levels alpha tests F laws p)⟩

include pairing unions powers separation carrier in
theorem flatSuccessorSmallInclusion_graph_mem :
    letI := smallOrder
    s.graph (pres) inc ∈ M.sets := by
  let := smallOrder
  rw [M.flatSuccessorSmallInclusion_graph]
  exact M.identityFunctionGraph_mem pairing unions powers separation carrier

theorem flatSuccessorNameLiftGraph_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    letI := smallOrder
    Name.renameFamilyGraph (pres) inc X oldValid = identityFunctionGraph X := by
  let := smallOrder
  apply ZFSet.ext
  intro z
  rw [Name.mem_renameFamilyGraph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨tau, member, equal⟩
    have sameCode := M.flatSuccessorNameLift_val c s I T levels alpha tests F laws tau
    exact ⟨tau.val, member, equal.trans (congrArg (ZFSet.pair tau.val) sameCode)⟩
  · rintro ⟨x, member, rfl⟩
    let tau : Name s := ⟨x, oldValid x member⟩
    refine ⟨tau, member, ?_⟩
    exact (congrArg (ZFSet.pair x) (M.flatSuccessorNameLift_val c s I T levels alpha tests F laws tau)).symm

include pairing unions powers separation in
theorem flatSuccessorNameLiftGraph_mem (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z)
    (ground : X ∈ M.sets) :
    letI := smallOrder
    Name.renameFamilyGraph (pres) inc X oldValid ∈ M.sets := by
  let := smallOrder
  rw [M.flatSuccessorNameLiftGraph_eq]
  exact M.identityFunctionGraph_mem pairing unions powers separation ground

noncomputable def flatSuccessorGroundNameLift (tau : (M.nameDomain s).names) : (M.nameDomain (pres)).names :=
  ⟨liftName tau.val, M.flatSuccessorNameLift_mem c s I T levels alpha tests F laws tau.val tau.property⟩

theorem flatSuccessorGroundNameLift_val (tau : (M.nameDomain s).names) :
    (M.flatSuccessorGroundNameLift c s I T levels alpha tests F laws tau).val.val = tau.val.val :=
  M.flatSuccessorNameLift_val c s I T levels alpha tests F laws tau.val

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
