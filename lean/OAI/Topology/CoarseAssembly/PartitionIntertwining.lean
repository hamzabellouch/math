import OAI.Topology.CoarseAssembly.RipsUnitaryLocalization

namespace OAI

/-! # Finite localization respects reducing isometric intertwiners -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X E H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partitionCompression_intertwines (I : E →ₗᵢ[ℂ] H)
    (a : X → E →L[ℂ] E) (b : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (hb : ∀ x, (b x).adjoint = b x)
    (hI : ∀ x v, b x (I v) = I (a x v))
    (F : E →L[ℂ] E) (G : H →L[ℂ] H) (hF : ∀ v, G (I v) = I (F v)) (v : E) :
    partitionCompression b G (I v) = I (partitionCompression a F v) := by
  simp only [partitionCompression_eq_sum, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [ha, hb, hI, hF, hI]

theorem localizedSpatialOperator_apply (a : X → E →L[ℂ] E)
    (ha : ∑ x, (a x).adjoint.comp (a x) = 1) (F : E →L[ℂ] E)
    (v : Module X E) (x : X) :
    localizedSpatialOperator a ha F v x =
      v x + a x ((partitionCompression a F - 1) (∑ y, (a y).adjoint (v y))) := by
  change v x + partitionIsometry a ha
    ((partitionCompression a F - 1) ((partitionIsometry a ha).toContinuousLinearMap.adjoint v)) x = _
  rw [partitionIsometry_apply, partitionIsometry_toContinuousLinearMap, partitionMap_adjoint_apply]

theorem localizedSpatialOperator_intertwines (I : E →ₗᵢ[ℂ] H)
    (a : X → E →L[ℂ] E) (b : X → H →L[ℂ] H)
    (ha : ∀ x, (a x).adjoint = a x) (hb : ∀ x, (b x).adjoint = b x)
    (hpa : ∑ x, (a x).adjoint.comp (a x) = 1)
    (hpb : ∑ x, (b x).adjoint.comp (b x) = 1)
    (hI : ∀ x v, b x (I v) = I (a x v))
    (F : E →L[ℂ] E) (G : H →L[ℂ] H) (hF : ∀ v, G (I v) = I (F v)) :
    (localizedSpatialOperator b hpb G).comp (coefficientIsometry I).toContinuousLinearMap =
      (coefficientIsometry I).toContinuousLinearMap.comp (localizedSpatialOperator a hpa F) := by
  ext v x
  change localizedSpatialOperator b hpb G (coefficientIsometry I v) x =
    I (localizedSpatialOperator a hpa F v x)
  rw [localizedSpatialOperator_apply, localizedSpatialOperator_apply]
  simp only [coefficientIsometry_apply, ha, hb]
  have hsum : (∑ y, b y (I (v y))) = I (∑ y, a y (v y)) := by
    simp only [hI, map_sum]
  rw [hsum]
  simp only [sub_apply, one_apply_eq_self, partitionCompression_intertwines I a b ha hb hI F G hF,
    ← map_sub, hI, map_add]

end CoarseAssembly.DiscreteRoe

end

end OAI
