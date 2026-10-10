import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalStageTwoSupport
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageTwoAtomicLifting
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageTwoProjectedFilters
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageTwoRefinementObjects

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoNameLiftingData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  support_data : StageTwoSupportData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  lifting :
    let actionData := support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
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
        let restriction := M.stageTwoSmallRestriction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first F
        let inclusion := M.stageTwoSmallInclusion c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
          next.indices.levelCode
        let liftName := M.stageTwoNameLift c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first F
          actionData.closure_data.projection_data.first_level next.indices.levelCode
        ∃ projection : CompleteProjection restriction inclusion,
          (∀ τ : Name s, (liftName τ).val = τ.val) ∧
          (∀ τ : Name s, τ.val ∈ M.sets → (liftName τ).val ∈ M.sets) ∧
          s.graph pres inclusion = identityFunctionGraph s.carrier ∧
          s.graph pres inclusion ∈ M.sets ∧
          (∀ Y (oldValid : ∀ z ∈ Y, IsName s z),
            Name.renameFamilyGraph pres inclusion Y oldValid = identityFunctionGraph Y ∧
            (Y ∈ M.sets → Name.renameFamilyGraph pres inclusion Y oldValid ∈ M.sets)) ∧
          (∀ (H : Set (Shrink Condition)) (τ : Name s),
            Name.eval H (liftName τ) = Name.eval {p | inclusion p ∈ H} τ) ∧
          (∀ (H : ConditionFilter (Shrink Condition)) (τ : Name s),
            Name.eval H.mem (liftName τ) = Name.eval (projection.projectedFilter H).mem τ) ∧
          (∀ H : ConditionFilter (Shrink Condition), H.GenericFor (M.codedFamily pres) →
            (projection.projectedFilter H).GenericFor (M.codedFamily s)) ∧
          (∀ (q : Shrink Condition) (σ τ : Name s),
            Name.ForcesEq q (liftName σ) (liftName τ) ↔ Name.ForcesEq (restriction q) σ τ) ∧
          (∀ (q : Shrink Condition) (σ τ : Name s),
            Name.ForcesMem q (liftName σ) (liftName τ) ↔ Name.ForcesMem (restriction q) σ τ) ∧
          (∀ g (τ : Name s), action.act pres g (liftName τ) = liftName (e.act s g τ)) ∧
          (∀ τ : Name s, action.stabilizer pres (liftName τ) = e.stabilizer s τ) ∧
          (∀ (supports : Compression.RecursiveMaps.NormalSubgroupFamily G) (τ : Name s),
            HereditarilySymmetric e s supports τ → HereditarilySymmetric action pres supports (liftName τ)) ∧
          Name.renamedFamily pres inclusion T next.valid1 = T ∧
          Name.renamedFamily pres inclusion T2 next.valid2 = T2 ∧
          ((∀ z ∈ T, IsName pres z) ∧
            (∀ g (τ : Name pres), τ.val ∈ T → (action.act pres g τ).val ∈ T) ∧
            (∀ τ : Name pres, τ.val ∈ T →
              HereditarilySymmetric action pres (d.principalSupportFamily base directed) τ)) ∧
          ((∀ z ∈ T2, IsName pres z) ∧
            (∀ g (τ : Name pres), τ.val ∈ T2 → (action.act pres g τ).val ∈ T2) ∧
            (∀ τ : Name pres, τ.val ∈ T2 →
              HereditarilySymmetric action pres (d.principalSupportFamily base directed) τ)) ∧
          T2 = orderedPairNameFamily (pres.encode ⊤) T T ∧
          ∀ n : Nat, iteratedPairNameFamily (pres.encode ⊤) T n =
            iteratedPairNameFamily (s.encode ⊤) T n

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageTwoNameLiftingData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageTwoSupportData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageTwoNameLiftingData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, _⟩ := actionData.actions
  refine ⟨prior, F, ?_⟩
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    data.terms_ground base directed next.first F first second
  refine ⟨hNodes, inputs, ?_⟩
  have projection := M.stageTwoSmallCompleteProjection c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    data.terms_ground base directed next.first F first second infinite choice hI0 next.indices.index_ground
  refine ⟨projection, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.stageTwoNameLift_val c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second
  · exact M.stageTwoNameLift_mem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second
  · exact M.stageTwoSmallInclusion_graph c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second
  · exact M.stageTwoSmallInclusion_graph_mem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second
  · intro Y oldValid
    exact ⟨M.stageTwoNameLiftGraph_eq c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second Y oldValid,
      M.stageTwoNameLiftGraph_mem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second Y oldValid⟩
  · exact M.stageTwoNameLift_eval c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second
  · exact M.stageTwoProjectedFilter_eval c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoProjectedFilter_codedGeneric c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second infinite choice hI0 next.indices.index_ground rows nodeOrder (M.omega_mem separation infinite)
  · exact M.stageTwoNameLift_forcesEq c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoNameLift_forcesMem c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoNameLift_act c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoNameLift_stabilizer c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoNameLift_hs c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoNameFamily_eq c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second T next.valid1
  · exact M.stageTwoNameFamily_eq c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second T2 next.valid2
  · exact M.stageTwoNameFamily_transport c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs infinite choice hI0 next.indices.index_ground (d.principalSupportFamily base directed) T next.valid1 next.inputs.terms_closed next.terms_hs
  · exact M.stageTwoNameFamily_transport c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second a image inputs infinite choice hI0 next.indices.index_ground (d.principalSupportFamily base directed) T2 next.valid2 next.inputs.pairs_closed next.pairs_hs
  · rw [M.stageTwo_orderedPairNameFamily c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second]
    exact data.index_data.square
  · exact M.stageTwo_iteratedPairNameFamily c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first F first second T

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

theorem exists_rowStageTwoNameLifting
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
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
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
                (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid)
                (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
                nextAction ∧
              (letI := M.stageOneConditionSmallTop act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
               let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
                 pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                 indexSystem ⊥ directed first collection
               StageTwoNameLiftingData M act c nextAction nextPres b s a ⊥ directed
                 lifted squared valid1 pairing unions powers separation collection
                 S mu s.nonbottom.carrier
                 (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid)
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
  have original := fulfilled.exists_rowStageTwoSupport collection infinite choice hK standard indices
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid
  exact M.stageTwoNameLiftingData act c nextAction nextPres b s a ⊥ directed
    lifted squared valid1 pairing unions powers separation collection S mu s.nonbottom.carrier tuples
    (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
    priorAction carrier indexSystem.index_ground order infinite choice

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
