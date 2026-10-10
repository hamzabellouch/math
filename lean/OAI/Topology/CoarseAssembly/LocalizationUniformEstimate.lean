import OAI.Topology.CoarseAssembly.SandwichNormControl

namespace OAI

/-! # A component-independent estimate for representation-varying localization -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Fintype X] [DecidableEq X] [CompleteSpace H] in
theorem constantBlock_sub (F G : H →L[ℂ] H) :
    constantBlock (X := X) F - constantBlock G = constantBlock (F - G) := by
  ext v x
  rfl

theorem partitionCompression_variation_norm_le (a b : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (F G : H →L[ℂ] H) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖partitionCompression a F - partitionCompression b G‖ ≤
      ‖F - G‖ + 2 * C * ‖partitionMap a - partitionMap b‖ := by
  have hP : ‖partitionMap a‖ ≤ 1 := (partitionIsometry a ha).norm_toContinuousLinearMap_le
  have hQ : ‖partitionMap b‖ ≤ 1 := (partitionIsometry b hb).norm_toContinuousLinearMap_le
  have hPa : ‖(partitionMap a).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hP
  have hQa : ‖(partitionMap b).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hQ
  have h := operatorSandwich_sub_norm_le (partitionMap a).adjoint (partitionMap b).adjoint
    hPa hQa (constantBlock F) (constantBlock G) C ((constantBlock_norm_le G).trans hG)
  have hd : ‖(partitionMap a).adjoint - (partitionMap b).adjoint‖ =
      ‖partitionMap a - partitionMap b‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  simp only [operatorSandwich, ContinuousLinearMap.adjoint_adjoint, hd,
    constantBlock_sub] at h
  exact h.trans (add_le_add (constantBlock_norm_le (F - G)) le_rfl)

theorem localizedSpatialOperator_eq_sandwich (a : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (F : H →L[ℂ] H) :
    localizedSpatialOperator a ha F =
      1 + operatorSandwich (partitionMap a) (partitionCompression a F - 1) := rfl

theorem localizedSpatialOperator_variation_norm_le (a b : X → H →L[ℂ] H)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (F G : H →L[ℂ] H) (C : ℝ) (hG : ‖G‖ ≤ C) :
    ‖localizedSpatialOperator a ha F - localizedSpatialOperator b hb G‖ ≤
      ‖F - G‖ + (4 * C + 2) * ‖partitionMap a - partitionMap b‖ := by
  have hP : ‖partitionMap a‖ ≤ 1 := (partitionIsometry a ha).norm_toContinuousLinearMap_le
  have hQ : ‖partitionMap b‖ ≤ 1 := (partitionIsometry b hb).norm_toContinuousLinearMap_le
  have hK : ‖partitionCompression b G - 1‖ ≤ C + 1 :=
    (norm_sub_le _ _).trans (add_le_add ((partitionCompression_norm_le b hb G).trans hG)
      ContinuousLinearMap.norm_id_le)
  have h := operatorSandwich_sub_norm_le (partitionMap a) (partitionMap b) hP hQ
    (partitionCompression a F - 1) (partitionCompression b G - 1) (C + 1) hK
  have hd : (partitionCompression a F - 1) - (partitionCompression b G - 1) =
      partitionCompression a F - partitionCompression b G := sub_sub_sub_cancel_right _ _ _
  have he : localizedSpatialOperator a ha F - localizedSpatialOperator b hb G =
      operatorSandwich (partitionMap a) (partitionCompression a F - 1) -
        operatorSandwich (partitionMap b) (partitionCompression b G - 1) := by
    simp only [localizedSpatialOperator_eq_sandwich, add_sub_add_left_eq_sub]
  rw [he]
  rw [hd] at h
  have hinner := partitionCompression_variation_norm_le a b ha hb F G C hG
  calc
    _ ≤ ‖partitionCompression a F - partitionCompression b G‖ +
        2 * (C + 1) * ‖partitionMap a - partitionMap b‖ := h
    _ ≤ (‖F - G‖ + 2 * C * ‖partitionMap a - partitionMap b‖) +
        2 * (C + 1) * ‖partitionMap a - partitionMap b‖ := add_le_add hinner le_rfl
    _ = _ := by ring

end CoarseAssembly.DiscreteRoe

end

end OAI
