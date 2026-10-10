import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneNameLifting
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRefinementSystem

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

theorem exists_rowStageOneForcing
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
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1 ∧
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2 ∧
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            (∀ C E (U Rf Rc : (M.nameDomain c.pairEmpty).names),
              refinementIndexCode ∅ (s.encode C) (s.encode E) U.val.val Rf.val.val Rc.val.val ∈
                M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid1 →
              RefinementObjectSystem M act c.pairEmpty (a.principalSupportFamily ⊥ directed)
                (a.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
            ∀ n : Nat, Name.renamedFamily c.pairEmpty id (iteratedPairNameFamily (c.encode ⊤) T n)
                (iteratedPairNameFamily_valid ⊤ valid n) =
              iteratedPairNameFamily (c.pairEmpty.encode ⊤) lifted n := by
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
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
      liftedGround, squaredGround, graphGround, injection, valid1, valid2,
      first, second, indexSystem, objects, finitePowers⟩ :=
    fulfilled.exists_rowRefinementSystem collection infinite choice hK standard indices
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, ?_, objects, finitePowers⟩
  exact M.stageOneForcing_mem act c s a _ _ valid1 pairing unions powers separation
    carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first
    order (M.omega_mem separation infinite)

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
