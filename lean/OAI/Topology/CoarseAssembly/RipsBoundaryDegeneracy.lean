import OAI.Topology.CoarseAssembly.AmpleRipsFamily
import OAI.Topology.CoarseAssembly.MultiplierBoundaryHomotopy

namespace OAI

/-! # Degenerate families have zero whole-union Roe boundary

Vanishing is proved from an exact global involution, not from vanishing of
the individual finite-component K-theory classes.
-/

noncomputable section

namespace CoarseAssembly

theorem isometricExtension_sq_eq_one {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : E →ₗᵢ[ℂ] H) (F : E →L[ℂ] E) (hF : F * F = 1) :
    isometricExtension V F * isometricExtension V F = 1 := by
  apply sub_eq_zero.mp
  rw [isometricExtension_square_defect, hF, sub_self]
  change operatorConjugationHom V 0 = 0
  exact map_zero _

namespace Analytic

theorem localizedOperator_degenerate {A : Type} [NonUnitalCStarAlgebra A]
    {ι : Type*} [Fintype ι] (c : OddCycle A) (a : ι → A) (hc : c.Degenerate)
    (hpart : ∑ i, c.representation (a i) * c.representation (a i) = 1) :
    localizedOperator c a = c.operator := by
  apply sub_eq_zero.mp
  rw [localizedOperator_sub_eq c a hpart]
  simp only [hc.1, mul_zero, Finset.sum_const_zero]

end Analytic

namespace Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]

theorem ripsCompression_degenerate (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    partitionCompression (representedSqrt r c) c.operator = c.operator := by
  rw [ripsCompression_eq_localized]
  apply localizedOperator_degenerate c _ hc
  simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, hπ]

theorem ripsSpatialOperator_degenerate_sq (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    ripsSpatialOperator r c hπ * ripsSpatialOperator r c hπ = 1 := by
  have hs : c.operator * c.operator = 1 := by
    have h := hc.2.1 1
    rw [hπ, mul_one] at h
    exact sub_eq_zero.mp h
  unfold ripsSpatialOperator localizedSpatialOperator
  apply isometricExtension_sq_eq_one
  rwa [ripsCompression_degenerate r c hπ hc]

theorem ampleRipsOperator_degenerate_sq (r : ℝ) (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hc : c.Degenerate) :
    ampleRipsOperator r c hπ * ampleRipsOperator r c hπ = 1 :=
  isometricExtension_sq_eq_one _ _ (ripsSpatialOperator_degenerate_sq r c hπ hc)

end Rips

namespace DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem separatedFamilyBoundary_involution (o : ∀ i, V i) (A : ∀ i, Operator (V i) H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hp : ∀ i, PropagationLE r (A i))
    (hself : ∀ i, IsSelfAdjoint (A i))
    (hsq : ∀ i, IsCompactOperator (A i * A i - (1 : Operator (V i) H)))
    (hinv : ∀ i, A i * A i = 1) :
    letI := separatedMetric o
    separatedFamilyBoundary o A C hC hA r hr hp hself hsq = 0 := by
  let := separatedMetric o
  refine multiplierBoundaryClass_eq_zero _
    (separatedFamilyMultiplier_selfAdjoint o A C hC hA r hr hp hself)
    (diagonalFamily_square_mem_roe o A C hC hA r hr hp hself hsq) ?_
  apply Subtype.ext
  change diagonalFamily A C hC hA * diagonalFamily A C hC hA = 1
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext z
  rcases z with ⟨i, x⟩
  have hi := DFunLike.congr_fun (hinv i) (rowVector v i)
  have hix := congrArg (fun w : Module (V i) H => w x) hi
  simpa only [mul_apply_eq_comp, one_apply_eq_self, diagonalFamily_apply,
    rowVector_diagonalFamily, rowVector] using hix

end DiscreteRoe

namespace Rips

open Analytic DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem ampleRipsFamilyBoundary_degenerate (o : ∀ i, V i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (C : ℝ) (hC : 0 ≤ C) (hnorm : ∀ i, ‖(c i).operator‖ ≤ C)
    (hc : ∀ i, (c i).Degenerate) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hnorm = 0 := by
  let := separatedMetric o
  exact separatedFamilyBoundary_involution o
    (fun i => ampleRipsOperator r (c i) (hπ i)) (C + 4) (by linarith)
    (fun i => (ampleRipsOperator_norm_le r (c i) (hπ i)).trans (by linarith [hnorm i]))
    (r + r) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c i) (hπ i))
    (fun i => ampleRipsOperator_selfAdjoint r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_square_compact r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_degenerate_sq r (c i) (hπ i) (hc i))

end Rips

end CoarseAssembly

end

end OAI
