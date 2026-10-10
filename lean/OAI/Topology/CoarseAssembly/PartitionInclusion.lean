import OAI.Topology.CoarseAssembly.RoeInclusion
import OAI.Topology.CoarseAssembly.SpatialLocalization

namespace OAI

/-! # Finite partition localization under vertex inclusions -/

noncomputable section

namespace CoarseAssembly

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem isometricExtension_comp (V : F →ₗᵢ[ℂ] G) (W : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    isometricExtension V (isometricExtension W T) = isometricExtension (V.comp W) T := by
  change 1 + operatorConjugation V (1 + operatorConjugation W (T - 1) - 1) =
    1 + operatorConjugation (V.comp W) (T - 1)
  rw [add_sub_cancel_left, operatorConjugation_comp]

namespace DiscreteRoe

variable {X Y H : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype Y] [DecidableEq Y] [CompleteSpace H] in
@[simp] theorem partitionMap_apply (a : X → H →L[ℂ] H) (v : H) (x : X) :
    partitionMap a v x = a x v := DFunLike.congr_fun (coordinate_partitionMap a x) v

omit [CompleteSpace H] in
theorem partitionMap_inclusion (e : X ↪ Y) (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) :
    (inclusionIsometry (H := H) e).toContinuousLinearMap.comp (partitionMap a) =
      partitionMap b := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change inclusionVector e (partitionMap a v) y = partitionMap b v y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, partitionMap_apply, partitionMap_apply, he]
  · rw [inclusionVector_zero e _ _ hy, partitionMap_apply, hz y hy, zero_apply]

theorem partitionIsometry_inclusion (e : X ↪ Y) (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ y, (b y).adjoint.comp (b y) = 1)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) :
    (inclusionIsometry e).comp (partitionIsometry a ha) = partitionIsometry b hb := by
  apply DFunLike.ext
  intro v
  exact DFunLike.congr_fun (partitionMap_inclusion e a b he hz) v

omit [Fintype Y] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_inclusion (e : X ↪ Y) (T : H →L[ℂ] H) :
    (constantBlock (X := Y) T).comp (inclusionIsometry e).toContinuousLinearMap =
      (inclusionIsometry e).toContinuousLinearMap.comp (constantBlock (X := X) T) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext y
  change T (inclusionVector e v y) = inclusionVector e (constantBlock T v) y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, inclusionVector_apply, constantBlock_apply]
  · rw [inclusionVector_zero e _ _ hy, inclusionVector_zero e _ _ hy, map_zero]

theorem partitionCompression_inclusion (e : X ↪ Y)
    (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) (T : H →L[ℂ] H) :
    partitionCompression b T = partitionCompression a T := by
  unfold partitionCompression
  rw [← partitionMap_inclusion e a b he hz, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro v
  change (partitionMap a).adjoint ((inclusionIsometry e).toContinuousLinearMap.adjoint
    (constantBlock T (inclusionIsometry e (partitionMap a v)))) =
      (partitionMap a).adjoint (constantBlock T (partitionMap a v))
  have h := DFunLike.congr_fun (constantBlock_inclusion e T) (partitionMap a v)
  change constantBlock T (inclusionIsometry e (partitionMap a v)) =
    inclusionIsometry e (constantBlock T (partitionMap a v)) at h
  rw [h, adjoint_apply_isometry]

theorem localizedSpatialOperator_inclusion (e : X ↪ Y)
    (a : X → H →L[ℂ] H) (b : Y → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ y, (b y).adjoint.comp (b y) = 1)
    (he : ∀ x, b (e x) = a x) (hz : ∀ y, y ∉ Set.range e → b y = 0) (T : H →L[ℂ] H) :
    localizedSpatialOperator b hb T =
      isometricExtension (inclusionIsometry e) (localizedSpatialOperator a ha T) := by
  unfold localizedSpatialOperator
  rw [isometricExtension_comp, partitionIsometry_inclusion e a b ha hb he hz,
    partitionCompression_inclusion e a b he hz]

end DiscreteRoe
end CoarseAssembly

end

end OAI
