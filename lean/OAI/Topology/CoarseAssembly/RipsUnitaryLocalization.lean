import OAI.Topology.CoarseAssembly.RipsEmbeddingIndependence
import OAI.Topology.CoarseAssembly.PartitionInclusion

namespace OAI

/-! # Unitary equivalence commutes with finite-Rips localization -/

noncomputable section

namespace CoarseAssembly

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricExtension_equiv (U : E ≃ₗᵢ[ℂ] H) (F : E →L[ℂ] E) :
    isometricExtension U.toLinearIsometry F = operatorConjugation U.toLinearIsometry F := by
  have h1 : operatorConjugation U.toLinearIsometry (1 : E →L[ℂ] E) = 1 := by
    have hU : U.toLinearIsometry.toContinuousLinearMap.adjoint =
        U.symm.toLinearIsometry.toContinuousLinearMap := LinearIsometryEquiv.adjoint_eq_symm U
    ext x
    simp [operatorConjugation, hU]
  change 1 + operatorConjugationHom U.toLinearIsometry (F - 1) = _
  rw [map_sub]
  change 1 + (operatorConjugation U.toLinearIsometry F -
    operatorConjugation U.toLinearIsometry 1) = _
  rw [h1]
  abel

namespace DiscreteRoe

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem partitionIsometry_apply (a : X → E →L[ℂ] E)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (v : E) (x : X) :
    partitionIsometry a ha v x = a x v := by
  exact DFunLike.congr_fun (coordinate_partitionMap a x) v

omit [CompleteSpace E] [CompleteSpace H] [Fintype X] [DecidableEq X] in
theorem coefficientIsometry_comp {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (V : H →ₗᵢ[ℂ] G) (W : E →ₗᵢ[ℂ] H) :
    (coefficientIsometry (X := X) V).comp (coefficientIsometry W) =
      coefficientIsometry (V.comp W) := by
  ext v x
  rfl

end DiscreteRoe

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d : OddCycle C(Point X r, ℂ)}

theorem ripsCompression_unitary (e : c.UnitaryEquivalent d) :
    partitionCompression (representedSqrt r d) d.operator =
      operatorConjugation e.unitary.toLinearIsometry
        (partitionCompression (representedSqrt r c) c.operator) := by
  rw [partitionCompression_eq_sum, partitionCompression_eq_sum]
  let φ := operatorConjugationHom e.unitary.toLinearIsometry
  have hr (x : X) : representedSqrt r d x = φ (representedSqrt r c x) :=
    e.representation_eq (sqrtCoordinate r x)
  have ho : d.operator = φ c.operator := e.operator_eq
  change (∑ x, star (representedSqrt r d x) * (d.operator * representedSqrt r d x)) =
    φ (∑ x, star (representedSqrt r c x) * (c.operator * representedSqrt r c x))
  simp only [hr, ho, ← map_star, ← map_mul, ← map_sum]

theorem partitionIsometry_unitary (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    (partitionIsometry (representedSqrt r d) (representedSqrt_partition r d hd)).comp
        e.unitary.toLinearIsometry =
      (coefficientIsometry e.unitary.toLinearIsometry).comp
        (partitionIsometry (representedSqrt r c) (representedSqrt_partition r c hc)) := by
  ext v x
  change partitionIsometry (representedSqrt r d) _ (e.unitary v) x =
    e.unitary (partitionIsometry (representedSqrt r c) _ v x)
  rw [partitionIsometry_apply, partitionIsometry_apply]
  rw [show representedSqrt r d x = operatorConjugation e.unitary.toLinearIsometry
    (representedSqrt r c x) from e.representation_eq (sqrtCoordinate r x)]
  have hU : e.unitary.toLinearIsometry.toContinuousLinearMap.adjoint =
      e.unitary.symm.toLinearIsometry.toContinuousLinearMap :=
    LinearIsometryEquiv.adjoint_eq_symm e.unitary
  simp [operatorConjugation, hU]

theorem ripsSpatialOperator_unitary (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ripsSpatialOperator r d hd =
      isometricExtension (coefficientIsometry e.unitary.toLinearIsometry)
        (ripsSpatialOperator r c hc) := by
  change isometricExtension (partitionIsometry (representedSqrt r d) _)
    (partitionCompression (representedSqrt r d) d.operator) =
      isometricExtension (coefficientIsometry e.unitary.toLinearIsometry)
        (isometricExtension (partitionIsometry (representedSqrt r c) _)
          (partitionCompression (representedSqrt r c) c.operator))
  rw [ripsCompression_unitary r e, ← isometricExtension_equiv e.unitary,
    isometricExtension_comp, isometricExtension_comp, partitionIsometry_unitary r e hc hd]

end Rips
end CoarseAssembly

end

end OAI
