import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRowOrdinaryZF

namespace OAI

section

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

theorem exists_rowNiceNameSystem
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
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
       let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      ∀ n : Nat, let terms := iteratedPairNameFamily (c.encode ⊤) T n
        terms ∈ M.sets ∧ GroundBelow M terms K ∧ ∃ valid : ∀ z ∈ terms, IsName c z,
          NiceNameSystem M act c s a ⊥ directed terms valid ∧
          let lifted := Name.renamedFamily c.pairEmpty id terms valid
          let graph := Name.renameFamilyGraph c.pairEmpty id terms valid
          lifted ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode terms lifted graph ∧
          ∃ liftedValid : ∀ z ∈ lifted, IsName c.pairEmpty z,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted liftedValid ∧
            ∀ (H : Set (SetMembers (M.smallPartialFunctions
              (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))) (x : ZFSet.{u}),
              (∃ τ : Name c.pairEmpty, τ.val ∈ lifted ∧ Name.eval H τ = x) ↔
                ∃ τ : Name c, τ.val ∈ terms ∧ Name.eval H τ = x := by
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
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, _, _, _, _, _, _, _, stageTerms⟩ :=
    fulfilled.exists_rowTermSystem collection infinite choice hK standard indices
  have baseValid := (stageTerms 0).2.2.1
  have baseClosed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ?_⟩
  intro n
  obtain ⟨ground, below, valid, children, _⟩ := stageTerms n
  refine ⟨ground, below, valid, ?_⟩
  exact M.pairEmpty_niceNameSystem act c b s a ⊥ directed pairing unions powers separation collection
    carrier forcingOrder geometry.actors_ground geometry.carrier_ground supports forcingAction
    _ ground valid (iteratedPairNameFamily_closed act baseValid baseClosed n) children

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
