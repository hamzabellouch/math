import OAI.Topology.CoarseAssembly.CoefficientIsometry
import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary
import OAI.Topology.CoarseAssembly.EmbeddingBoundaryComparison

namespace OAI

/-! # A single source Hilbert sum for all choices of ample coefficients -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {Q : ℕ → Type} [∀ i, DecidableEq (Q i)]
  {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def familyCoefficientIsometry (V : ∀ i, E i →ₗᵢ[ℂ] H) :
    lp (fun i => Module (Q i) (E i)) 2 →ₗᵢ[ℂ] Module (Sigma Q) H :=
  (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.comp
    (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i)))

omit [∀ i, DecidableEq (Q i)] [∀ i, CompleteSpace (E i)] [CompleteSpace H] in
@[simp] theorem familyCoefficientIsometry_apply (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (v : lp (fun i => Module (Q i) (E i)) 2) (i : ℕ) (x : Q i) :
    familyCoefficientIsometry V v ⟨i, x⟩ = V i (v i x) := rfl

omit [∀ i, DecidableEq (Q i)] in
theorem familyCoefficientIsometry_adjoint_apply (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (v : Module (Sigma Q) H) (i : ℕ) (x : Q i) :
    (familyCoefficientIsometry V).toContinuousLinearMap.adjoint v i x =
      (V i).toContinuousLinearMap.adjoint (v ⟨i, x⟩) := by
  have he : (familyCoefficientIsometry (Q := Q) V).toContinuousLinearMap =
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.toContinuousLinearMap.comp
        (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap := rfl
  have hflat :
      (flattenEquiv (Q := Q) (H := H)).toLinearIsometry.toContinuousLinearMap.adjoint =
        (flattenEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap := by
    exact LinearIsometryEquiv.adjoint_eq_symm (flattenEquiv (Q := Q) (H := H))
  have hadj : (familyCoefficientIsometry (Q := Q) V).toContinuousLinearMap.adjoint =
      (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap.adjoint.comp
        (flattenEquiv (Q := Q) (H := H)).symm.toLinearIsometry.toContinuousLinearMap := by
    rw [he, ContinuousLinearMap.adjoint_comp, hflat]
  have hx := congrArg (fun T : Module (Sigma Q) H →L[ℂ] lp (fun i => Module (Q i) (E i)) 2 =>
    T v i x) hadj
  change _ = _ at hx
  rw [hx]
  change (blockIsometry (fun i => coefficientIsometry (X := Q i) (V i))).toContinuousLinearMap.adjoint
    (unflattenVector v) i x = _
  rw [blockIsometry_toCLM, blockOperator_adjoint]
  exact coefficientIsometry_adjoint_apply (V i) (rowVector v i) x

theorem familyEmbeddingTransition_propagation (V W : ∀ i, E i →ₗᵢ[ℂ] H)
    [PseudoMetricSpace (Sigma Q)] :
    PropagationLE 0 (embeddingTransition (familyCoefficientIsometry (Q := Q) V)
      (familyCoefficientIsometry W)) := by
  intro x y hxy
  have hne : x ≠ y := by rintro rfl; simp at hxy
  rcases x with ⟨i, x⟩
  ext h
  change familyCoefficientIsometry W
    ((familyCoefficientIsometry V).toContinuousLinearMap.adjoint (lp.single 2 y h)) ⟨i, x⟩ = 0
  rw [familyCoefficientIsometry_apply, familyCoefficientIsometry_adjoint_apply]
  simp [lp.single_apply, hne]

omit [∀ i, DecidableEq (Q i)] in
theorem familyCoefficient_extension (V : ∀ i, E i →ₗᵢ[ℂ] H)
    (A : ∀ i, Operator (Q i) (E i)) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (D : ℝ) (hD : 0 ≤ D) (hB : ∀ i, ‖coefficientExtension (V i) (A i)‖ ≤ D) :
    isometricExtension (familyCoefficientIsometry V) (blockOperator A C hC hA) =
      diagonalFamily (fun i => coefficientExtension (V i) (A i)) D hD hB := by
  ext v p
  rcases p with ⟨i, x⟩
  have hr : (familyCoefficientIsometry V).toContinuousLinearMap.adjoint v i =
      (coefficientIsometry (X := Q i) (V i)).toContinuousLinearMap.adjoint (rowVector v i) := by
    apply lp.ext
    funext y
    rw [familyCoefficientIsometry_adjoint_apply, coefficientIsometry_adjoint_apply]
    rfl
  change v ⟨i, x⟩ + familyCoefficientIsometry V
    ((blockOperator A C hC hA - 1)
      ((familyCoefficientIsometry V).toContinuousLinearMap.adjoint v)) ⟨i, x⟩ =
    coefficientExtension (V i) (A i) (rowVector v i) x
  rw [familyCoefficientIsometry_apply]
  simp only [sub_apply, blockOperator_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply]
  rw [hr]
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem blockOperator_selfAdjoint (A : ∀ i, Operator (Q i) (E i))
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) (hs : ∀ i, IsSelfAdjoint (A i)) :
    IsSelfAdjoint (blockOperator A C hC hA) := by
  change (blockOperator A C hC hA).adjoint = _
  rw [blockOperator_adjoint]
  ext v i x
  change (A i).adjoint (v i) x = A i (v i) x
  rw [show (A i).adjoint = A i from (hs i).star_eq]

end CoarseAssembly.DiscreteRoe

end

end OAI
