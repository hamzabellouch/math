import OAI.RepresentationTheory.VertexAlgebra.AlgebraCovariance
import OAI.RepresentationTheory.VertexAlgebra.MobiusStandardAction
import OAI.RepresentationTheory.VertexAlgebra.ProjectiveTopology

namespace OAI

noncomputable section
open Set
open scoped Topology MatrixGroups
namespace StronglyRationalVOA
namespace SmoothCircleDiffeomorphism
 
def action : SmoothCircleDiffeomorphism →* Equiv.Perm (AddCircle (2*Real.pi)) :=
  QuotientGroup.lift SmoothCircleLift.circleAction.ker SmoothCircleLift.circleAction
    (fun _ h => h)
@[simp] lemma action_mk (F : SmoothCircleLift) (x : AddCircle (2*Real.pi)) :
    action (QuotientGroup.mk F) x=F.onCircle x := rfl
lemma maps_arc (F : SmoothCircleDiffeomorphism) (I : ProperCircleArc) :
    ∃ J : ProperCircleArc, J.carrier=action F '' I.carrier := by
  induction F using QuotientGroup.induction_on with
  | H F => exact ⟨F.mapArc I,F.mapArc_carrier I⟩
end SmoothCircleDiffeomorphism

 
def projectiveConjugation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : ProjectiveUnitaryGroup H → ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) :=
  Quotient.lift (fun E : H ≃ₗᵢ[ℂ] H => E.conjStarAlgEquiv) (by
    intro E F h
    exact projective_equality_conjugation E F (Quotient.sound h))
@[simp] lemma projectiveConjugation_mk {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (E : H ≃ₗᵢ[ℂ] H) :
    projectiveConjugation (QuotientGroup.mk E)=E.conjStarAlgEquiv := rfl

 

def globalObservableAlgebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) :
    Subalgebra ℂ (H →L[ℂ] H) :=
  Algebra.adjoin ℂ (⋃ I, (N I : Set (H →L[ℂ] H)))
 
def globalCyclicSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ B ∈ globalObservableAlgebra N, x=B Ω}).topologicalClosure

 

structure IrreducibleConformalNetStructure {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : ProperCircleArc → VonNeumannAlgebra H) where
  separable : TopologicalSpace.SeparableSpace H
  carrier_congr : ∀ I J, I.carrier=J.carrier → N I=N J
  isotony : ∀ I J, I.carrier ⊆ J.carrier → N I ≤ N J
  locality : ∀ I J, Disjoint I.carrier J.carrier → N I ≤ (N J).commutant
  mobius : PSL(2,ℝ) →* (H ≃ₗᵢ[ℂ] H)
  mobius_continuous : Continuous mobius
  diffeomorphism : SmoothCircleDiffeomorphism →* ProjectiveUnitaryGroup H
  diffeomorphism_continuous : Continuous diffeomorphism
  extends_mobius : ∀ F, diffeomorphism (CircleMobiusGeometry.inclusion (CircleMobiusGeometry.projectiveStandardAction F))=QuotientGroup.mk (mobius F)
  covariance : ∀ F I J, J.carrier=SmoothCircleDiffeomorphism.action F '' I.carrier →
    ∀ B : H →L[ℂ] H, projectiveConjugation (diffeomorphism F) B ∈ N J ↔ B ∈ N I
  local_action : ∀ F I, (∀ x ∈ I.carrier, SmoothCircleDiffeomorphism.action F x=x) →
    ∀ B ∈ N I, projectiveConjugation (diffeomorphism F) B=B
  vacuum : H
  vacuum_norm : ‖vacuum‖=1
  vacuum_invariant : ∀ F, mobius F vacuum=vacuum
  vacuum_unique : ∀ x : H, (∀ F, mobius F x=x) → ∃ c : ℂ, x=c • vacuum
  vacuum_cyclic : globalCyclicSpace N vacuum=⊤
  hamiltonian : H →ₗ.[ℂ] H
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  positive_energy : ∀ x y, (x,y) ∈ hamiltonian.graph → 0 ≤ (inner ℂ x y).re
  rotation_flow : ∀ t : ℝ,
    (mobius (QuotientGroup.mk (CircleMobiusGeometry.rotationMatrix t))).toLinearIsometry.toContinuousLinearMap=
      SymmetricOperator.flow hamiltonian hamiltonian_selfAdjoint t
  irreducible : ∀ Q : H →L[ℂ] H, (∀ I, Q ∈ (N I).commutant) →
    ∃ c : ℂ, Q=c • (1 : H →L[ℂ] H)
end StronglyRationalVOA

end

end OAI
