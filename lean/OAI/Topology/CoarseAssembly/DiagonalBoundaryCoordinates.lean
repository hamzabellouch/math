import OAI.Topology.CoarseAssembly.SeparatedFamilyBoundary
import OAI.Topology.CoarseAssembly.CayleyIntertwining

namespace OAI

/-! # Coordinates of the whole-union rational boundary unitary -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type*} [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rowRestriction (i : ℕ) : Module (Sigma V) H →L[ℂ] Module (V i) H :=
  (lp.evalCLM ℂ (fun j => Module (V j) H) 2 i).comp
    (flattenEquiv (Q := V) (H := H)).symm.toLinearIsometry.toContinuousLinearMap

omit [∀ i, DecidableEq (V i)] [CompleteSpace H] in
@[simp] theorem rowRestriction_apply (i : ℕ) (v : Module (Sigma V) H) :
    rowRestriction i v = rowVector v i := rfl

omit [∀ i, DecidableEq (V i)] in
theorem row_rationalBoundaryUnitary (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (hself : ∀ i, IsSelfAdjoint (A i)) (v : Module (Sigma V) H) (i : ℕ) :
    rowVector ((rationalBoundaryUnitary (diagonalFamily A C hC hA)
      (diagonalFamily_selfAdjoint A C hC hA hself) : Operator (Sigma V) H) v) i =
      (rationalBoundaryUnitary (A i) (hself i) : Operator (V i) H) (rowVector v i) :=
  rationalBoundaryUnitary_intertwines (rowRestriction i) _ _ _ _
    (fun w => rowVector_diagonalFamily A C hC hA w i) v

variable [PseudoMetricSpace (Sigma V)]

theorem row_multiplierBoundaryUnitary
    (F : multiplierAlgebra (X := Sigma V) (H := H)) (hF : IsSelfAdjoint F)
    (A : ∀ i, Operator (V i) H) (hself : ∀ i, IsSelfAdjoint (A i))
    (hrow : ∀ v i, rowVector ((F : Operator (Sigma V) H) v) i = A i (rowVector v i))
    (v : Module (Sigma V) H) (i : ℕ) :
    rowVector ((multiplierBoundaryUnitary F hF : Operator (Sigma V) H) v) i =
      (rationalBoundaryUnitary (A i) (hself i) : Operator (V i) H) (rowVector v i) := by
  let φ := (multiplierAlgebra (X := Sigma V) (H := H)).subtype
  have hm := map_rationalBoundaryUnitary φ F hF
  change rowVector (φ (rationalBoundaryUnitary F hF) v) i = _
  rw [hm]
  exact rationalBoundaryUnitary_intertwines (rowRestriction i) (F : Operator (Sigma V) H)
    (A i) (hF.map φ) (hself i) (fun w => hrow w i) v

end CoarseAssembly.DiscreteRoe

end

end OAI
