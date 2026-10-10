import OAI.Topology.CoarseAssembly.ProjectionUnitaryPath

namespace OAI

/-! # An explicit path from the identity to a self-adjoint involution -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

def involutionNegativeProjection (U : A) : A := (1 / 2 : ℂ) • (1 - U)

theorem involutionNegativeProjection_isStarProjection (U : A)
    (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    IsStarProjection (involutionNegativeProjection U) := by
  have hs : (1 - U) * (1 - U) = (2 : ℂ) • (1 - U) := by
    calc
      _ = 1 - U - U + U * U := by noncomm_ring
      _ = _ := by rw [hUU]; module
  constructor
  · change ((1 / 2 : ℂ) • (1 - U)) * ((1 / 2 : ℂ) • (1 - U)) =
      (1 / 2 : ℂ) • (1 - U)
    rw [smul_mul_assoc, mul_smul_comm, hs, smul_smul, smul_smul]
    norm_num
  · change star ((1 / 2 : ℂ) • (1 - U)) = (1 / 2 : ℂ) • (1 - U)
    simp only [star_smul, star_sub, star_one, hU.star_eq]
    norm_num

def involutionUnitaryPath (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    Interval → unitary A :=
  projectionSignPath (involutionNegativeProjection U)
    (involutionNegativeProjection_isStarProjection U hU hUU)

theorem involutionUnitaryPath_continuous [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousSMul ℂ A] (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    Continuous (involutionUnitaryPath U hU hUU) := projectionSignPath_continuous _ _

@[simp] theorem involutionUnitaryPath_start (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    involutionUnitaryPath U hU hUU start = 1 := projectionSignPath_start _ _

@[simp] theorem involutionUnitaryPath_finish (U : A) (hU : IsSelfAdjoint U) (hUU : U * U = 1) :
    (involutionUnitaryPath U hU hUU finish : A) = U := by
  change (projectionSignPath (involutionNegativeProjection U)
    (involutionNegativeProjection_isStarProjection U hU hUU) finish : A) = U
  rw [projectionSignPath_finish]
  unfold involutionNegativeProjection
  rw [smul_smul]
  norm_num

end CoarseAssembly.Analytic

end

end OAI
