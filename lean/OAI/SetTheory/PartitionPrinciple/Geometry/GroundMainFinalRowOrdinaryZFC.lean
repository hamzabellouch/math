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

theorem exists_rowModel_ordinaryZFC
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
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
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 ∧
      ZFRealization (M.ordinaryExtension c H).sets ∧
      CollectionSchema (M.ordinaryExtension c H).sets ∧
      Realize (M.ordinaryExtension c H).sets SetFormula.choice Fin.elim0 ∧
      ∀ U ∈ M.sets, GroundSequenceReflection M (M.ordinaryExtension c H) U := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice, reflection⟩ :=
    fulfilled.exists_rowModel_sequenceReflection collection infinite groundChoice small p
  have axioms := M.countableFunction_ordinaryZFC pairing unions powers separation collection infinite
    groundChoice
    (M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns)
    (M.natSetCode_mem separation infinite 2) H ordinary
  exact ⟨H, hp, coded, ordinary, symmetric, includes, zf, noChoice,
    axioms.1, axioms.2.1, axioms.2.2, reflection⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
