import OAI.Topology.CoarseAssembly.DiagonalBoundaryCoordinates
import OAI.Topology.CoarseAssembly.SeparatedFamilyPerturbation
import OAI.Topology.CoarseAssembly.OperatorNormalization

namespace OAI

/-! # Removing finitely many components from the whole-union boundary

The argument works with the actual rational boundary unitary. Involutive
components contribute the identity in that unitary, before taking K-theory.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem relativeClass_congr {B : Type*} [CStarAlgebra B]
    (S : NonUnitalStarSubalgebra ℂ B) [hS : IsClosed (S : Set B)]
    (u v : unitary B) (hu : (u : B) - 1 ∈ S) (hv : (v : B) - 1 ∈ S) (h : u = v) :
    OperatorKTheory.relativeClass S u hu = OperatorKTheory.relativeClass S v hv := by
  subst v
  rfl

theorem separatedFamilyBoundary_eq_of_rational (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (hAB : ∀ i, rationalBoundaryUnitary (A i) (hAs i) = rationalBoundaryUnitary (B i) (hBs i)) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  let := separatedMetric o
  let F := separatedFamilyMultiplier o A C hC hA r hr hp
  let G := separatedFamilyMultiplier o B D hD hB s hs hq
  have hFs : IsSelfAdjoint F := separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hAs
  have hGs : IsSelfAdjoint G := separatedFamilyMultiplier_selfAdjoint o B D hD hB s hs hq hBs
  have hu : multiplierBoundaryUnitary F hFs = multiplierBoundaryUnitary G hGs := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext z
    rcases z with ⟨i, x⟩
    have h1 := congrArg (fun w : Module (V i) H => w x)
      (row_multiplierBoundaryUnitary F hFs A hAs
        (fun w j => rowVector_diagonalFamily A C hC hA w j) v i)
    have h2 := congrArg (fun w : Module (V i) H => w x)
      (row_multiplierBoundaryUnitary G hGs B hBs
        (fun w j => rowVector_diagonalFamily B D hD hB w j) v i)
    exact h1.trans ((congrArg (fun u : unitary (Operator (V i) H) =>
      (u : Operator (V i) H) (rowVector v i) x) (hAB i)).trans h2.symm)
  exact relativeClass_congr (hS := algebra_isClosed) _ _ _ _ _ hu

/-- The finite head can differ arbitrarily when its operators are exact
involutions. Equality is proved for the entire Roe boundary. -/
theorem separatedFamilyBoundary_eq_of_involutive_head (o : ∀ i, V i)
    (A B : ∀ i, Operator (V i) H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ∀ i, ‖A i‖ ≤ C) (hB : ∀ i, ‖B i‖ ≤ D)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ i, PropagationLE r (A i)) (hq : ∀ i, PropagationLE s (B i))
    (hAs : ∀ i, IsSelfAdjoint (A i)) (hBs : ∀ i, IsSelfAdjoint (B i))
    (hAsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hBsq : ∀ i, IsCompactOperator (B i * B i - (1 : Operator (V i) H)))
    (J : Finset ℕ) (htail : ∀ i, i ∉ J → A i = B i)
    (hAi : ∀ i, i ∈ J → A i * A i = 1) (hBi : ∀ i, i ∈ J → B i * B i = 1) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hAs hAsq =
      separatedFamilyBoundary o B D hD hB s hs hq hBs hBsq := by
  apply separatedFamilyBoundary_eq_of_rational o A B C D hC hD hA hB r s hr hs hp hq hAs hBs hAsq hBsq
  intro i
  by_cases hi : i ∈ J
  · exact (rationalBoundaryUnitary_eq_one (A i) (hAs i) (hAi i hi)).trans
      (rationalBoundaryUnitary_eq_one (B i) (hBs i) (hBi i hi)).symm
  · have hcongr (T U : Operator (V i) H) (hT : IsSelfAdjoint T) (hU : IsSelfAdjoint U)
        (he : T = U) : rationalBoundaryUnitary T hT = rationalBoundaryUnitary U hU := by
      subst U
      rfl
    exact hcongr _ _ _ _ (htail i hi)

end CoarseAssembly.DiscreteRoe

end

end OAI
