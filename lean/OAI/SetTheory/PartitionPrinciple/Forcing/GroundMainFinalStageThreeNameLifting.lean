import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFlatSuccessorAtomicTransfer
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFlatSuccessorProjectedFilters
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalStageThreeSupport

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
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
variable {G : Type v} [Group G]
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs

theorem flatSuccessorNameLift_hs (supports : NormalSubgroupFamily G) (τ : Name s)
    (hs : HereditarilySymmetric lowerAction s supports τ) :
    letI := smallOrder
    HereditarilySymmetric (smallAct) (pres) supports (liftName τ) := by
  let := smallOrder
  exact hs.rename (smallAct) (pres) inc
    (fun g p => (M.flatSuccessorSmallInclusion_equivariant c s I T levels alpha tests
      rowAction lowerAction image inputs F laws g p).symm)

include F laws in
theorem flatSuccessorNameFamily_valid (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    ∀ z ∈ X, IsName (pres) z := by
  intro z hz
  have lifted := (liftName ⟨z, oldValid z hz⟩).property
  rw [M.flatSuccessorNameLift_val c s I T levels alpha tests F laws ⟨z, oldValid z hz⟩] at lifted
  exact lifted

theorem flatSuccessorNameFamily_eq (X : ZFSet.{u}) (oldValid : ∀ z ∈ X, IsName s z) :
    Name.renamedFamily (pres) inc X oldValid = X := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily]
  constructor
  · rintro ⟨τ, hτ, equal⟩
    have codes := M.flatSuccessorNameLift_val c s I T levels alpha tests F laws τ
    exact (equal.trans codes).symm ▸ hτ
  · intro hz
    exact ⟨⟨z, oldValid z hz⟩, hz,
      (M.flatSuccessorNameLift_val c s I T levels alpha tests F laws ⟨z, oldValid z hz⟩).symm⟩

include F laws in
theorem flatSuccessorNameFamily_transport (supports : NormalSubgroupFamily G) (X : ZFSet.{u})
    (oldValid : ∀ z ∈ X, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ X → (lowerAction.act s g τ).val ∈ X)
    (children : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric lowerAction s supports τ) :
    letI := smallOrder
    (∀ z ∈ X, IsName (pres) z) ∧
      (∀ g (τ : Name (pres)), τ.val ∈ X → ((smallAct).act (pres) g τ).val ∈ X) ∧
      (∀ τ : Name (pres), τ.val ∈ X → HereditarilySymmetric (smallAct) (pres) supports τ) := by
  let := smallOrder
  refine ⟨M.flatSuccessorNameFamily_valid c s I T levels alpha tests F laws X oldValid, ?_, ?_⟩
  · intro g τ hτ
    let σ : Name s := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.flatSuccessorNameLift_val c s I T levels alpha tests F laws σ)
    rw [← same, M.flatSuccessorNameLift_act c s I T levels alpha tests F laws
      rowAction lowerAction image inputs, M.flatSuccessorNameLift_val]
    exact closed g σ hτ
  · intro τ hτ
    let σ : Name s := ⟨τ.val, oldValid τ.val hτ⟩
    have same : liftName σ = τ := Subtype.ext
      (M.flatSuccessorNameLift_val c s I T levels alpha tests F laws σ)
    rw [← same]
    exact M.flatSuccessorNameLift_hs c s I T levels alpha tests F laws
      rowAction lowerAction image inputs supports σ (children σ hτ)

variable [OrderTop P]
local notation "smallTop" => M.flatSuccessorSmallTop c s I T levels alpha tests F laws

theorem flatSuccessor_orderedPairNameFamily (X Y : ZFSet.{u}) :
    letI := smallOrder
    letI := smallTop
    orderedPairNameFamily ((pres).encode ⊤) X Y = orderedPairNameFamily (s.encode ⊤) X Y := by
  let := smallOrder
  let := smallTop
  rw [M.flatSuccessorPresentation_top]

theorem flatSuccessor_iteratedPairNameFamily (X : ZFSet.{u}) (n : Nat) :
    letI := smallOrder
    letI := smallTop
    iteratedPairNameFamily ((pres).encode ⊤) X n = iteratedPairNameFamily (s.encode ⊤) X n := by
  let := smallOrder
  let := smallTop
  rw [M.flatSuccessorPresentation_top]

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable {G : Type v} {R P : Type u} [Group G]
variable [PartialOrder R] [PartialOrder P]

structure FlatSuccessorNameLiftingData (M : TransitiveGround.{u})
    (c : Presentation R) (s : Presentation P)
    (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
    {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
    (laws : FlatSuccessorLaws Jold I T levels alpha tests)
    (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
    (image : G → ZFSet.{u} → ZFSet.{u})
    (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image) : Prop where
  codes : ∀ tau : Name s,
    (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau).val = tau.val
  inclusion_graph :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    s.graph (M.flatSuccessorPresentation c s I T levels alpha tests)
      (M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws) = identityFunctionGraph s.carrier
  inclusion_ground :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    s.graph (M.flatSuccessorPresentation c s I T levels alpha tests)
      (M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws) ∈ M.sets
  family_graph :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (X : ZFSet.{u}) (valid : ∀ z ∈ X, IsName s z),
      Name.renameFamilyGraph (M.flatSuccessorPresentation c s I T levels alpha tests)
        (M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws) X valid = identityFunctionGraph X
  family_ground :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (X : ZFSet.{u}) (valid : ∀ z ∈ X, IsName s z), X ∈ M.sets →
      Name.renameFamilyGraph (M.flatSuccessorPresentation c s I T levels alpha tests)
        (M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws) X valid ∈ M.sets
  projection :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    CompleteProjection (M.flatSuccessorSmallRestriction c s I T levels alpha tests F)
      (M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws)
  eval :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (H : Set (Shrink (FlatSuccessorCondition M c s I T levels alpha tests))) (tau : Name s),
      Name.eval H (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) =
        Name.eval {p | M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws p ∈ H} tau
  projected_membership :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (H : ConditionFilter (Shrink (FlatSuccessorCondition M c s I T levels alpha tests))) (p : P),
      (projection.projectedFilter H).mem p ↔ ∃ q, H.mem q ∧
        M.flatSuccessorSmallRestriction c s I T levels alpha tests F q = p
  projected_eval :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (H : ConditionFilter (Shrink (FlatSuccessorCondition M c s I T levels alpha tests))) (tau : Name s),
      Name.eval H.mem (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) =
        Name.eval (projection.projectedFilter H).mem tau
  projected_generic :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (H : ConditionFilter (Shrink (FlatSuccessorCondition M c s I T levels alpha tests))),
      H.GenericFor (M.codedFamily (M.flatSuccessorPresentation c s I T levels alpha tests)) →
        (projection.projectedFilter H).GenericFor (M.codedFamily s)
  forcesEq :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (q : Shrink (FlatSuccessorCondition M c s I T levels alpha tests)) (sigma tau : Name s),
      Name.ForcesEq q (M.flatSuccessorNameLift c s I T levels alpha tests F laws sigma)
        (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) ↔
      Name.ForcesEq (M.flatSuccessorSmallRestriction c s I T levels alpha tests F q) sigma tau
  forcesMem :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (q : Shrink (FlatSuccessorCondition M c s I T levels alpha tests)) (sigma tau : Name s),
      Name.ForcesMem q (M.flatSuccessorNameLift c s I T levels alpha tests F laws sigma)
        (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) ↔
      Name.ForcesMem (M.flatSuccessorSmallRestriction c s I T levels alpha tests F q) sigma tau
  act :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (g : G) (tau : Name s),
      (M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs).act
        (M.flatSuccessorPresentation c s I T levels alpha tests) g
        (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) =
      M.flatSuccessorNameLift c s I T levels alpha tests F laws (lowerAction.act s g tau)
  stabilizer :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ tau : Name s,
      (M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs).stabilizer
        (M.flatSuccessorPresentation c s I T levels alpha tests)
        (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau) = lowerAction.stabilizer s tau
  hereditary :
    letI := M.flatSuccessorSmallOrder c s I T levels alpha tests
    ∀ (supports : NormalSubgroupFamily G) (tau : Name s),
      HereditarilySymmetric lowerAction s supports tau →
        HereditarilySymmetric
          (M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs)
          (M.flatSuccessorPresentation c s I T levels alpha tests) supports
          (M.flatSuccessorNameLift c s I T levels alpha tests F laws tau)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u v
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
variable {G : Type v} [Group G]
variable (rowAction : PosetAction G R) (lowerAction : PosetAction G P)
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : FlatSuccessorActionInputs M c s I T levels alpha tests rowAction lowerAction image)
local notation "smallAct" => M.flatSuccessorSmallAction c s I T levels alpha tests rowAction lowerAction image inputs

theorem flatSuccessorNameLiftingData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (lower : s.carrier ∈ M.sets)
    (upper : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets) :
    FlatSuccessorNameLiftingData M c s I T levels alpha tests F laws
      rowAction lowerAction image inputs := by
  let := smallOrder
  exact {
    codes := M.flatSuccessorNameLift_val c s I T levels alpha tests F laws
    inclusion_graph := M.flatSuccessorSmallInclusion_graph c s I T levels alpha tests F laws
    inclusion_ground := M.flatSuccessorSmallInclusion_graph_mem c s I T levels alpha tests F laws
      pairing unions powers separation lower
    family_graph := M.flatSuccessorNameLiftGraph_eq c s I T levels alpha tests F laws
    family_ground := M.flatSuccessorNameLiftGraph_mem c s I T levels alpha tests F laws
      pairing unions powers separation
    projection := M.flatSuccessorSmallCompleteProjection c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha
    eval := M.flatSuccessorNameLift_eval c s I T levels alpha tests F laws
    projected_membership := M.flatSuccessorProjectedFilter_mem_iff c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha
    projected_eval := M.flatSuccessorProjectedFilter_eval c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha
    projected_generic := M.flatSuccessorProjectedFilter_codedGeneric c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha lower upper
    forcesEq := M.flatSuccessorNameLift_forcesEq c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha
    forcesMem := M.flatSuccessorNameLift_forcesMem c s I T levels alpha tests F laws
      pairing unions powers separation infinite choice hLevels hAlpha
    act := M.flatSuccessorNameLift_act c s I T levels alpha tests F laws rowAction lowerAction image inputs
    stabilizer := M.flatSuccessorNameLift_stabilizer c s I T levels alpha tests F laws rowAction lowerAction image inputs
    hereditary := M.flatSuccessorNameLift_hs c s I T levels alpha tests F laws rowAction lowerAction image inputs }

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeNameLiftingData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  support_data : StageThreeSupportData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  lifting :
    let actionData := support_data.action_data.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
        next.indices.levelCode
      ∃ hNodes : nodes.carrier ∈ M.sets,
      ∃ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first
        let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first a image inputs
        ∃ next2 : RefinementStageSystem M action pres actors nodes d base directed (natSetCode 2) T T2,
          let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
          let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
          let levels := stageThreeAssignmentLevels I0 I1 I2 T
          ∃ hCarrier : pres.carrier ∈ M.sets, ∃ hOrder : pres.conditionOrder ∈ M.sets,
          let tests := M.refinementLevelTests pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1
            action nodes d base directed next2.first (natSetCode 2) T2
          let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
            pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
            hNodes prior.terms_ground next.indices base directed next.first
          let laws := M.stageThreeFlatSuccessorLaws pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1 action nodes d base directed next2.first
            actionData.closure_data.projection_data.first_level next.indices.levelCode next2.indices.levelCode
          letI := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          letI := M.flatSuccessorSmallTop c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
          let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let inclusion := M.flatSuccessorSmallInclusion c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
          let image3 := M.stageThreeAssignmentImage a c.pairEmpty e s action pres nodes d T T2
            valid actionData.valid2 next.valid1 next.valid2 next2.valid1 next2.valid2
          ∃ inputs3 : FlatSuccessorActionInputs M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
            a action image3,
            let action3 := M.flatSuccessorSmallAction c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
              a action image3 inputs3
            TransitiveGround.FlatSuccessorNameLiftingData M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
              F2 laws a action image3 inputs3 ∧
            Name.renamedFamily pres3 inclusion T next2.valid1 = T ∧
            Name.renamedFamily pres3 inclusion T2 next2.valid2 = T2 ∧
            ((∀ z ∈ T, IsName pres3 z) ∧
              (∀ g (τ : Name pres3), τ.val ∈ T → (action3.act pres3 g τ).val ∈ T) ∧
              (∀ τ : Name pres3, τ.val ∈ T →
                HereditarilySymmetric action3 pres3 (d.principalSupportFamily base directed) τ)) ∧
            ((∀ z ∈ T2, IsName pres3 z) ∧
              (∀ g (τ : Name pres3), τ.val ∈ T2 → (action3.act pres3 g τ).val ∈ T2) ∧
              (∀ τ : Name pres3, τ.val ∈ T2 →
                HereditarilySymmetric action3 pres3 (d.principalSupportFamily base directed) τ)) ∧
            T2 = orderedPairNameFamily (pres3.encode ⊤) T T ∧
            ∀ n : Nat, iteratedPairNameFamily (pres3.encode ⊤) T n =
              iteratedPairNameFamily (pres.encode ⊤) T n

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageThreeNameLiftingData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageThreeSupportData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageThreeNameLiftingData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.action_data.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, next2, hCarrier, hOrder, inputs3, _⟩ := prior.support
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first F first second
  let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
  let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first a image inputs
  let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
  let levels := stageThreeAssignmentLevels I0 I1 I2 T
  let tests := M.refinementLevelTests pres pairing unions powers separation collection hCarrier hOrder
    data.terms_ground next2.valid1 action nodes d base directed next2.first (natSetCode 2) T2
  let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    hNodes data.terms_ground next.indices base directed next.first
  let laws := M.stageThreeFlatSuccessorLaws pres pairing unions powers separation collection
    hCarrier hOrder data.terms_ground next2.valid1 action nodes d base directed next2.first
    first second next2.indices.levelCode
  let image3 := M.stageThreeAssignmentImage a c.pairEmpty e s action pres nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2 next2.valid1 next2.valid2
  let := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  let := M.flatSuccessorSmallTop c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws
  have hLevels := M.stageThreeAssignmentLevels_mem pairing unions powers separation
    hI0 next.indices.index_ground next2.indices.index_ground data.terms_ground
  have hAlpha := M.natSetCode_mem separation infinite 2
  have conditions := M.stageThreeFlatPresentation_carrier_mem c I0 I1 action pres nodes d T T2 next2.valid1
    pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
    next2.indices base directed next2.first rows hI0 next.indices.index_ground nodeOrder
    (M.omega_mem separation infinite)
  refine ⟨prior, F, hNodes, inputs, next2, hCarrier, hOrder, inputs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.flatSuccessorNameLiftingData c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws a action image3 inputs3 pairing unions powers separation infinite choice
      hLevels hAlpha hCarrier conditions
  · exact M.flatSuccessorNameFamily_eq c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws T next2.valid1
  · exact M.flatSuccessorNameFamily_eq c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws T2 next2.valid2
  · exact M.flatSuccessorNameFamily_transport c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws a action image3 inputs3 (d.principalSupportFamily base directed) T
      next2.valid1 next2.inputs.terms_closed next2.terms_hs
  · exact M.flatSuccessorNameFamily_transport c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws a action image3 inputs3 (d.principalSupportFamily base directed) T2
      next2.valid2 next2.inputs.pairs_closed next2.pairs_hs
  · rw [M.flatSuccessor_orderedPairNameFamily c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2 laws]
    rw [M.stageTwo_orderedPairNameFamily c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
      hNodes data.terms_ground next.indices base directed next.first F first second]
    exact data.index_data.square
  · exact M.flatSuccessor_iteratedPairNameFamily c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
      F2 laws T

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowStageThreeNameLifting
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let hCoordinates := M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
    let hTwo := M.natSetCode_mem separation infinite 2
    let hRow := M.countablePartialFunctions_mem pairing unions powers separation infinite hCoordinates hTwo
    let hOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite hCoordinates hTwo
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        (∃ hLifted : lifted ∈ M.sets, ∃ hSquared : squared ∈ M.sets, graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            ∃ first : NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            ∃ indexSystem : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2,
            ∃ inputs : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid1,
            act.conditionMapFamily c b ∈ M.sets ∧
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            M.stageOneForcingOrder act c s a lifted squared valid1 ∈ M.sets ∧
            (letI := M.stageOneConditionSmallOrder act c s a lifted squared valid1
              pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
             ∃ nextAction,
              nextAction = M.stageOneSmallAction act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted indexSystem ⊥ directed first
                collection b inputs hSquared (M.omega_mem separation infinite) ∧
              TransitiveGround.StageOneSmallActionLaws M act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection nextAction ∧
              nextAction.actionGraph
                (M.stageOneConditionPresentation act c s a lifted squared valid1
                  pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                  indexSystem ⊥ directed first collection) b ∈ M.sets ∧
              nextAction.conditionMapFamily
                (M.stageOneConditionPresentation act c s a lifted squared valid1
                  pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                  indexSystem ⊥ directed first collection) b ∈ M.sets ∧
              InternallyCountablyClosed M
              (M.stageOneConditionPresentation act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection) ∧
              TransitiveGround.StageOnePositionSupport M act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
                S mu s.nonbottom.carrier
                (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
                (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
                nextAction ∧
              (letI := M.stageOneConditionSmallTop act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
               let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
                 pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                 indexSystem ⊥ directed first collection
               StageThreeNameLiftingData M act c nextAction nextPres b s a ⊥ directed
                 lifted squared valid1 pairing unions powers separation collection
                 S mu s.nonbottom.carrier
                 (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
                 (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p)))) ∧
            (∀ C E (U Rf Rc : (M.nameDomain c.pairEmpty).names),
              refinementIndexCode ∅ (s.encode C) (s.encode E) U.val.val Rf.val.val Rc.val.val ∈
                M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid1 →
              RefinementObjectSystem M act c.pairEmpty (a.principalSupportFamily ⊥ directed)
                (a.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
            ∀ n : Nat, Name.renamedFamily c.pairEmpty id (iteratedPairNameFamily (c.encode ⊤) T n)
                (iteratedPairNameFamily_valid ⊤ valid n) =
              iteratedPairNameFamily (c.pairEmpty.encode ⊤) lifted n) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have original := fulfilled.exists_rowStageThreeSupport collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, data⟩ := data
  refine data.elim (fun valid data => ?_)
  refine data.elim (fun liftedGround data => ?_)
  refine data.elim (fun squaredGround data => ?_)
  obtain ⟨graphGround, injection, data⟩ := data
  refine data.elim (fun valid1 data => ?_)
  refine data.elim (fun valid2 data => ?_)
  refine data.elim (fun first data => ?_)
  obtain ⟨second, data⟩ := data
  refine data.elim (fun indexSystem data => ?_)
  refine data.elim (fun inputs data => ?_)
  obtain ⟨originalMaps, forcingGround, orderGround, actionData, objects, finitePowers⟩ := data
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, inputs, originalMaps,
    forcingGround, orderGround, ?_, objects, finitePowers⟩
  let lifted := Name.renamedFamily c.pairEmpty id _ valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  obtain ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, priorAction⟩ := actionData
  refine ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, ?_⟩
  let := M.stageOneConditionSmallTop act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
    pairing unions powers separation carrier forcingOrder geometry.carrier_ground liftedGround
    indexSystem ⊥ directed first collection
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  exact M.stageThreeNameLiftingData act c nextAction nextPres b s a ⊥ directed
    lifted squared valid1 pairing unions powers separation collection S mu s.nonbottom.carrier tuples
    (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
    priorAction carrier indexSystem.index_ground order infinite choice

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
