import OAI.Topology.CoarseAssembly.ComponentInclusion
import OAI.Topology.CoarseAssembly.DiagonalSpatialFamily
import OAI.Topology.CoarseAssembly.IsometricExtension

namespace OAI

/-! # Componentwise and whole-union spatial inclusions agree -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem componentEmbedding_range (e : ∀ i, Q i ↪ P i) (i : ℕ) (y : P i) :
    (⟨i, y⟩ : Sigma P) ∈ Set.range (componentEmbedding e) ↔ y ∈ Set.range (e i) := by
  constructor
  · rintro ⟨⟨j, x⟩, h⟩
    have hij : j = i := congrArg Sigma.fst h
    subst j
    refine ⟨x, ?_⟩
    change (⟨i, e i x⟩ : Sigma P) = ⟨i, y⟩ at h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  · rintro ⟨x, rfl⟩
    exact ⟨⟨i, x⟩, rfl⟩

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] in
theorem row_inclusion_adjoint (e : ∀ i, Q i ↪ P i) (v : Module (Sigma P) H) (i : ℕ) :
    rowVector ((inclusionIsometry (H := H) (componentEmbedding e)).toContinuousLinearMap.adjoint v) i =
      (inclusionIsometry (H := H) (e i)).toContinuousLinearMap.adjoint (rowVector v i) := by
  apply lp.ext
  funext x
  change ((inclusionIsometry (H := H) (componentEmbedding e)).toContinuousLinearMap.adjoint v) ⟨i, x⟩ =
    ((inclusionIsometry (H := H) (e i)).toContinuousLinearMap.adjoint (rowVector v i)) x
  rw [inclusion_adjoint_apply, inclusion_adjoint_apply]
  rfl

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] [CompleteSpace H]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem row_inclusion (e : ∀ i, Q i ↪ P i) (v : Module (Sigma Q) H) (i : ℕ) :
    rowVector (inclusionIsometry (H := H) (componentEmbedding e) v) i =
      inclusionIsometry (H := H) (e i) (rowVector v i) := by
  apply lp.ext
  funext y
  by_cases hy : y ∈ Set.range (e i)
  · obtain ⟨x, rfl⟩ := hy
    change inclusionVector (componentEmbedding e) v (componentEmbedding e ⟨i, x⟩) =
      inclusionVector (e i) (rowVector v i) (e i x)
    rw [inclusionVector_apply, inclusionVector_apply]
    rfl
  · have hglobal : (⟨i, y⟩ : Sigma P) ∉ Set.range (componentEmbedding e) :=
      fun h => hy ((componentEmbedding_range e i y).mp h)
    change inclusionVector (componentEmbedding e) v ⟨i, y⟩ =
      inclusionVector (e i) (rowVector v i) y
    rw [inclusionVector_zero _ _ _ hglobal, inclusionVector_zero _ _ _ hy]

omit [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)] in
theorem row_isometricExtension (e : ∀ i, Q i ↪ P i) (T : Operator (Sigma Q) H)
    (A : ∀ i, Operator (Q i) H)
    (hT : ∀ v i, rowVector (T v) i = A i (rowVector v i))
    (v : Module (Sigma P) H) (i : ℕ) :
    rowVector (isometricExtension (inclusionIsometry (componentEmbedding e)) T v) i =
      isometricExtension (inclusionIsometry (e i)) (A i) (rowVector v i) := by
  apply lp.ext
  funext y
  change (rowVector (v + operatorConjugation (inclusionIsometry (componentEmbedding e)) (T - 1) v) i) y = _
  change v ⟨i, y⟩ +
    (rowVector (inclusionIsometry (componentEmbedding e)
      ((T - 1) ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v))) i) y = _
  rw [row_inclusion]
  have hsub : rowVector ((T - 1)
      ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v)) i =
      (A i - 1) ((inclusionIsometry (e i)).toContinuousLinearMap.adjoint (rowVector v i)) := by
    apply lp.ext
    funext x
    change rowVector (T ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v)) i x -
      rowVector ((inclusionIsometry (componentEmbedding e)).toContinuousLinearMap.adjoint v) i x = _
    rw [hT, row_inclusion_adjoint]
    rfl
  rw [hsub]
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
