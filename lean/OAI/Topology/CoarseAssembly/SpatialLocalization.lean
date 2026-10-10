import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.PartitionSpatialControl
import OAI.Topology.CoarseAssembly.IsometricExtension
import OAI.Topology.CoarseAssembly.UnitalStructureAlgebra

namespace OAI

/-! # The controlled spatial representative of a localized operator -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationContinuousAdd

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationRingHomCompTriple

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.spatialLocalizationCompleteSpace

theorem partitionConjugate_eq (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    partitionConjugate a F = operatorConjugation (partitionIsometry a hpart) F := by
  rfl

theorem localizedSpatialOperator_eq (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    localizedSpatialOperator a hpart F =
      1 + partitionConjugate a (partitionCompression a F) - partitionConjugate a 1 := by
  rw [partitionConjugate_eq a hpart, partitionConjugate_eq a hpart]
  change 1 + operatorConjugationHom (partitionIsometry a hpart) (partitionCompression a F - 1) =
    1 + operatorConjugationHom (partitionIsometry a hpart) (partitionCompression a F) -
      operatorConjugationHom (partitionIsometry a hpart) 1
  rw [map_sub, add_sub_assoc]

theorem partitionCompression_selfAdjoint (a : X → H →L[ℂ] H)
    (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : IsSelfAdjoint (partitionCompression a F) := by
  rw [partitionCompression_eq_sum]
  exact isSelfAdjoint_sum _ (fun x _ => hF.conjugate' (a x))

theorem localizedSpatialOperator_selfAdjoint (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (localizedSpatialOperator a hpart F) :=
  isometricExtension_selfAdjoint _ _ (partitionCompression_selfAdjoint a F hF)

theorem localizedSpatialOperator_norm_le (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    ‖localizedSpatialOperator a hpart F‖ ≤ ‖F‖ + 2 :=
  (isometricExtension_norm_le _ _).trans
    (add_le_add (partitionCompression_norm_le a hpart F) le_rfl)

variable [PseudoMetricSpace X]

omit [Fintype X] [CompleteSpace H] [PseudoMetricSpace X] in
theorem entry_sub (T S : Operator X H) (x y : X) :
    entry (T - S) x y = entry T x y - entry S x y := by
  ext v
  simp [entry]

theorem localizedSpatialOperator_propagation (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1)
    (ha : ∀ x, (a x).adjoint = a x) (r : ℝ) (hr : 0 ≤ r)
    (hsupport : ∀ x y, r < dist x y → a x * a y = 0) (F : H →L[ℂ] H) :
    PropagationLE (r + r) (localizedSpatialOperator a hpart F) := by
  intro x y hxy
  rw [localizedSpatialOperator_eq, entry_sub, entry_add,
    partitionLocalization_propagation a ha r hsupport F x y hxy,
    partitionConjugate_one_propagation a ha r hsupport x y (by linarith),
    add_zero, sub_zero]
  exact propagationLE_one x y (by linarith)

end CoarseAssembly.DiscreteRoe

end

end OAI
