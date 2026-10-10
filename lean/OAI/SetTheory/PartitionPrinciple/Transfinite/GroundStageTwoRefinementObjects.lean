import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNameLiftFamilies

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

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "smallTop" => M.stageTwoConditionSmallTop c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

theorem stageTwo_orderedPairNameFamily (X Y : ZFSet.{u}) :
    letI := smallOrder
    letI := smallTop
    orderedPairNameFamily ((pres).encode ⊤) X Y =
      orderedPairNameFamily (s.encode ⊤) X Y := by
  let := smallOrder
  let := smallTop
  rw [M.stageTwoConditionPresentation_top c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second]

theorem stageTwo_iteratedPairNameFamily (X : ZFSet.{u}) (n : Nat) :
    letI := smallOrder
    letI := smallTop
    iteratedPairNameFamily ((pres).encode ⊤) X n =
      iteratedPairNameFamily (s.encode ⊤) X n := by
  let := smallOrder
  let := smallTop
  rw [M.stageTwoConditionPresentation_top c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second]

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

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "incl" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

local notation "smallTop" => M.stageTwoConditionSmallTop c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

include F first second infinite choice hI0 hI1 in
theorem stageTwoRefinementStageSystem
    (t : Presentation G)
    (parameters : StageOneActionParameters M a s t b d T T2 valid)
    (hT2 : T2 ∈ M.sets)
    (rows : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : letI := smallOrder; (smallAct).conditionMapFamily (pres) t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (children1 : ∀ τ : Name s, τ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ)
    (children2 : ∀ τ : Name s, τ.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ) :
    letI := smallOrder
    letI := smallTop
    RefinementStageSystem M (smallAct) (pres) t b d base directed (natSetCode 2) T T2 := by
  let := smallOrder
  let := smallTop
  obtain ⟨nextValid1, nextClosed1, nextHS1⟩ :=
    M.stageTwoNameFamily_transport c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second
      rowAction image inputs infinite choice hI0 hI1
      (d.principalSupportFamily base directed) T valid parameters.terms_closed children1
  obtain ⟨nextValid2, nextClosed2, nextHS2⟩ :=
    M.stageTwoNameFamily_transport c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second
      rowAction image inputs infinite choice hI0 hI1
      (d.principalSupportFamily base directed) T2 valid2 parameters.pairs_closed children2
  have omega := M.omega_mem separation infinite
  have nextCarrier : (pres).carrier ∈ M.sets :=
    M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid pairing unions powers separation
      rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega
  have nextOrder := M.stageTwoConditionOrder_mem c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    rows hI0 rowOrder nodeOrder omega
  exact M.refinementStageSystem (smallAct) (pres) t b d base directed
    pairing unions powers separation collection nextCarrier nextOrder group nodes nodeOrder maps
    parameters.node_maps supports (M.natSetCode_mem separation infinite 2) hT hT2
    nextValid1 nextValid2 nextClosed1 nextClosed2 nextHS1 nextHS2

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

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "incl" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

local notation "smallTop" => M.stageTwoConditionSmallTop c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

include infinite hI0 in
theorem stageTwoRefinementObjects
    (t : Presentation G)
    (next :
      letI := M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order hT base directed system
      letI := M.stageTwoConditionSmallTop c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order hT base directed system F first second
      RefinementStageSystem M
        (M.stageTwoSmallAction c I0 a s b d T T2 valid pairing unions powers separation
          collection carrier order hT base directed system rowAction image inputs)
        (M.stageTwoConditionPresentation c I0 a s b d T T2 valid pairing unions powers separation
          collection carrier order nodes hT indices base directed system)
        t b d base directed (natSetCode 2) T T2)
    (hT2 : T2 ∈ M.sets)
    (rows : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) :
    letI := smallOrder
    letI := smallTop
    ∀ C E (U Rf Rc : (M.nameDomain (pres)).names),
      refinementIndexCode (natSetCode 2) (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈
          M.niceRefinementIndices (smallAct) (pres) b d (natSetCode 2) T T2 next.valid1 →
      RefinementObjectSystem M (smallAct) (pres) (d.principalSupportFamily base directed)
        (d.principalFix C) T next.valid1 U.val Rf.val Rc.val := by
  let := smallOrder
  let := smallTop
  have omega := M.omega_mem separation infinite
  have nextCarrier : (pres).carrier ∈ M.sets :=
    M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid pairing unions powers separation
      rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega
  have nextOrder := M.stageTwoConditionOrder_mem c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    rows hI0 rowOrder nodeOrder omega
  exact (M.niceRefinementObjects (smallAct) (pres) b d base directed
    pairing unions powers separation collection (M.natSetCode_mem separation infinite 2)
    hT hT2 nextCarrier nextOrder nodes nodeOrder next.inputs.terms_closed next.terms_hs
    next.first next.second).2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
