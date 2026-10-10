import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FiniteRips
import OAI.Topology.CoarseAssembly.FiniteLocalization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

namespace OAI

/-! # The explicit square partition on a finite Rips realization -/

noncomputable section

namespace CoarseAssembly.Rips

variable {X : Type} [PseudoMetricSpace X] [Fintype X] (r : ℝ)

omit [Fintype X] in
@[simp] theorem sqrtCoordinate_selfAdjoint (x : X) :
    IsSelfAdjoint (sqrtCoordinate r x) := by
  ext p
  simp [sqrtCoordinate]

theorem sqrtCoordinate_square_sum :
    ∑ x : X, sqrtCoordinate r x * sqrtCoordinate r x = 1 := by
  ext p
  change (ContinuousMap.evalAlgHom ℂ ℂ p)
    (∑ x : X, sqrtCoordinate r x * sqrtCoordinate r x) = 1
  rw [map_sum]
  simp only [map_mul]
  change (∑ x : X, (Real.sqrt (p.weight x) : ℂ) * (Real.sqrt (p.weight x) : ℂ)) = 1
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt (p.nonneg _)]
  rw [← Complex.ofReal_sum, p.sum_weight, Complex.ofReal_one]

omit [Fintype X] in
theorem sqrtCoordinate_mul_eq_zero (x y : X) (hxy : r < dist x y) :
    sqrtCoordinate r x * sqrtCoordinate r y = 0 := by
  ext p
  have hz : p.weight x = 0 ∨ p.weight y = 0 := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hxy) (p.diameter x (Finsupp.mem_support_iff.mpr h.1)
      y (Finsupp.mem_support_iff.mpr h.2))
  rcases hz with hx | hy
  · simp [sqrtCoordinate, hx]
  · simp [sqrtCoordinate, hy]

theorem represented_sqrtCoordinate_square_sum
    {H : Analytic.HilbertSpace} (π : C(Point X r, ℂ) →⋆ₐ[ℂ] Analytic.End H) :
    ∑ x, π (sqrtCoordinate r x) * π (sqrtCoordinate r x) = 1 := by
  simp only [← map_mul, ← map_sum, sqrtCoordinate_square_sum, map_one]

end CoarseAssembly.Rips

end

end OAI
