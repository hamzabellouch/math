import OAI.RepresentationTheory.VertexAlgebra.NetVacuum
import OAI.RepresentationTheory.VertexAlgebra.MobiusContinuity
import OAI.RepresentationTheory.VertexAlgebra.RotationImplementer
import OAI.RepresentationTheory.VertexAlgebra.FixedArc
import OAI.RepresentationTheory.VertexAlgebra.MobiusStandardTopology

namespace OAI

noncomputable section
open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def conformalNetStructure (hc : A.toVertexAlgebra.C2Cofinite) :
    IrreducibleConformalNetStructure (U.intervalAlgebra hc) where
  separable := U.hilbertCompletion_separable
  carrier_congr := by
    intro I J h
    exact congrArg (U.localAlgebra hc) h
  isotony := by
    intro I J h
    exact U.localAlgebra_isotone hc h
  locality := by
    intro I J h
    exact U.localAlgebra_locality hc I.isOpen_carrier J.isOpen_carrier h
  mobius := (U.mobiusRepresentation hc).comp CircleMobiusGeometry.projectiveStandardAction
  mobius_continuous := (U.mobiusRepresentation_continuous hc).comp CircleMobiusGeometry.projectiveStandardAction_continuous
  diffeomorphism := U.diffeomorphismProjectiveRepresentation hc
  diffeomorphism_continuous := U.diffeomorphismProjectiveRepresentation_continuous hc
  extends_mobius := fun F => (U.mobiusRepresentation_projective hc (CircleMobiusGeometry.projectiveStandardAction F)).symm
  covariance := by
    intro F
    induction F using QuotientGroup.induction_on with
    | H F =>
      intro I J h B
      change (U.diffeomorphismImplementer hc F).conjStarAlgEquiv B ∈
        U.localAlgebra hc J.carrier ↔ B ∈ U.localAlgebra hc I.carrier
      change J.carrier=F.onCircle '' I.carrier at h
      rw [h]
      exact U.localAlgebra_diffeomorphism_iff hc F I.isOpen_carrier B
  local_action := by
    intro F
    induction F using QuotientGroup.induction_on with
    | H F =>
      intro I h B hB
      exact U.diffeomorphism_local_action hc F I h hB
  vacuum := (A.vacuum:Completion V)
  vacuum_norm := U.completion_vacuum_norm
  vacuum_invariant := fun F => U.mobiusRepresentation_vacuum hc _
  vacuum_unique := by
    intro x hx
    apply U.rotation_fixed_scalar
    intro t
    rw [← U.mobiusRepresentation_rotation hc t]
    simpa only [MonoidHom.comp_apply,CircleMobiusGeometry.projectiveStandardAction_rotation] using
      hx (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))
  vacuum_cyclic := U.interval_vacuum_cyclic hc
  hamiltonian := U.conformalHamiltonian
  hamiltonian_selfAdjoint := U.energyOperator_selfAdjoint (fun d => d)
  positive_energy := fun _ _ h => U.conformalHamiltonian_nonnegative h
  rotation_flow := by
    intro t
    apply ContinuousLinearMap.ext
    intro x
    change U.mobiusRepresentation hc
      (CircleMobiusGeometry.projectiveStandardAction (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))) x=_
    rw [CircleMobiusGeometry.projectiveStandardAction_rotation]
    rw [U.mobiusRepresentation_rotation,U.rotation_eq_hamiltonianFlow]
  irreducible := by
    intro Q hQ
    exact U.interval_commutant_scalar hc hQ
 

theorem cklwStrongLocal_and_conformalNet (hc : A.toVertexAlgebra.C2Cofinite) :
    U.CKLWStrongLocal hc ∧ Nonempty (IrreducibleConformalNetStructure (U.intervalAlgebra hc)) :=
  ⟨U.cklwStrongLocal hc,⟨U.conformalNetStructure hc⟩⟩
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
