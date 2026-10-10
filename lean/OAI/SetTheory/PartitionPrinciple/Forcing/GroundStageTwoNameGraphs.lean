import OAI.SetTheory.PartitionPrinciple.Transfinite.StageTwoClosureData

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

noncomputable def stageTwoNameLift (tau : Name s) : Name (pres) := by
  letI := smallOrder
  exact Name.rename (pres) inc tau

local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second

theorem stageTwoNameLift_val (tau : Name s) : (liftName tau).val = tau.val := by
  let := smallOrder
  exact Name.rename_val_of_encode (pres) inc
    (M.stageTwoSmallInclusion_encode c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second) tau

theorem stageTwoNameLift_mem (tau : Name s) (ground : tau.val ∈ M.sets) :
    (liftName tau).val ∈ M.sets := by
  rw [M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second]
  exact ground

theorem stageTwoNameLift_eval :
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

local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second

theorem stageTwoSmallInclusion_graph :
    letI := smallOrder
    s.graph (pres) inc = identityFunctionGraph s.carrier := by
  let := smallOrder
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨p, rfl⟩
    rw [M.stageTwoSmallInclusion_encode]
    exact ⟨s.encode p, s.encode_mem p, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, congrArg (ZFSet.pair (s.encode p))
      (M.stageTwoSmallInclusion_encode c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order nodes hT indices base directed system
        F first second p)⟩

theorem stageTwoSmallInclusion_graph_mem :
    letI := smallOrder
    s.graph (pres) inc ∈ M.sets := by
  let := smallOrder
  rw [M.stageTwoSmallInclusion_graph]
  exact M.identityFunctionGraph_mem pairing unions powers separation carrier

theorem stageTwoNameLiftGraph_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    letI := smallOrder
    Name.renameFamilyGraph (pres) inc X oldValid = identityFunctionGraph X := by
  let := smallOrder
  apply ZFSet.ext
  intro z
  rw [Name.mem_renameFamilyGraph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨tau, member, equal⟩
    have sameCode := M.stageTwoNameLift_val c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      F first second tau
    exact ⟨tau.val, member, equal.trans (congrArg (ZFSet.pair tau.val) sameCode)⟩
  · rintro ⟨x, member, rfl⟩
    let tau : Name s := ⟨x, oldValid x member⟩
    refine ⟨tau, member, ?_⟩
    exact (congrArg (ZFSet.pair x) (M.stageTwoNameLift_val c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      F first second tau)).symm

theorem stageTwoNameLiftGraph_mem (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z)
    (ground : X ∈ M.sets) :
    letI := smallOrder
    Name.renameFamilyGraph (pres) inc X oldValid ∈ M.sets := by
  let := smallOrder
  rw [M.stageTwoNameLiftGraph_eq]
  exact M.identityFunctionGraph_mem pairing unions powers separation ground

noncomputable def stageTwoGroundNameLift (tau : (M.nameDomain s).names) : (M.nameDomain (pres)).names :=
  ⟨liftName tau.val, M.stageTwoNameLift_mem c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F first second tau.val tau.property⟩

theorem stageTwoGroundNameLift_val (tau : (M.nameDomain s).names) :
    (M.stageTwoGroundNameLift c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order nodes hT indices base directed system
      F first second tau).val.val = tau.val.val :=
  M.stageTwoNameLift_val c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F first second tau.val

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
