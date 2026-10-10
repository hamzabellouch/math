import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNamePositionSupports

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

include infinite choice hI0 hI1 in
theorem stageTwoNameLift_hs (supports : NormalSubgroupFamily G) (τ : Name s)
    (hs : HereditarilySymmetric a s supports τ) :
    letI := smallOrder
    HereditarilySymmetric (smallAct) (pres) supports (liftName τ) := by
  let := smallOrder
  exact hs.rename (smallAct) (pres) incl
    (fun g p => (M.stageTwoSmallInclusion_equivariant c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system
      rowAction image inputs F first second infinite choice hI0 hI1 g p).symm)

include F first second in
theorem stageTwoNameFamily_valid (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    ∀ z ∈ X, IsName (pres) z := by
  intro z hz
  have lifted := (liftName ⟨z, oldValid z hz⟩).property
  erw [M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second] at lifted
  exact lifted

theorem stageTwoNameFamily_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    Name.renamedFamily (pres) incl X oldValid = X := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily]
  constructor
  · rintro ⟨τ, hτ, equal⟩
    have codes := M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second τ
    exact (equal.trans codes).symm ▸ hτ
  · intro hz
    exact ⟨⟨z, oldValid z hz⟩, hz,
      (M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second ⟨z, oldValid z hz⟩).symm⟩

include F first second infinite choice hI0 hI1 in
theorem stageTwoNameFamily_transport (supports : NormalSubgroupFamily G) (X : ZFSet.{u})
    (oldValid : ∀ z ∈ X, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ X → (a.act s g τ).val ∈ X)
    (children : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric a s supports τ) :
    letI := smallOrder
    (∀ z ∈ X, IsName (pres) z) ∧
      (∀ g (τ : Name (pres)), τ.val ∈ X → ((smallAct).act (pres) g τ).val ∈ X) ∧
      (∀ τ : Name (pres), τ.val ∈ X → HereditarilySymmetric (smallAct) (pres) supports τ) := by
  let := smallOrder
  refine ⟨M.stageTwoNameFamily_valid c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second X oldValid, ?_, ?_⟩
  · intro g τ hτ
    let σ : Name s := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second σ)
    rw [← same, M.stageTwoNameLift_act c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second rowAction image inputs infinite choice hI0 hI1,
      M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second]
    exact closed g σ hτ
  · intro τ hτ
    let σ : Name s := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second σ)
    rw [← same]
    exact M.stageTwoNameLift_hs c I0 a s b d T T2 valid pairing unions powers separation collection carrier order nodes hT indices base directed system F first second rowAction image inputs infinite choice hI0 hI1 supports σ (children σ hτ)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
