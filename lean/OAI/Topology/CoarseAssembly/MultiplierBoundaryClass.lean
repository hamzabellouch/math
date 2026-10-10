import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RoeIdealizer
import OAI.Topology.CoarseAssembly.CayleyBoundary
import OAI.Topology.CoarseAssembly.RelativeUnitary

namespace OAI

/-! # Boundary classes in the closed Roe multiplier algebra

A controlled Rips operator is a Roe multiplier even when it is not
pseudolocal for the discrete vertex representation. The ideal-boundary
construction is therefore performed in this actual closed multiplier
algebra before constructing the coarse assembly map.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
local instance : ContinuousStar (Operator X H) := ⟨operator_star_continuous⟩

theorem roeIdealizer_one : (1 : Operator X H) ∈ roeIdealizer (X := X) (H := H) := by
  intro S
  constructor
  · simpa only [one_mul] using S.property
  · simpa only [mul_one] using S.property

theorem multiplierAlgebra_closed :
    IsClosed (multiplierAlgebra (X := X) (H := H) : Set (Operator X H)) := roeIdealizer_closed

@[simp] theorem mem_multiplierRoeIdeal (T : multiplierAlgebra (X := X) (H := H)) :
    T ∈ multiplierRoeIdeal (X := X) (H := H) ↔ T.val ∈ algebra (X := X) (H := H) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

theorem multiplierBoundaryUnitary_sub_one_mem
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    (multiplierBoundaryUnitary F hF : Operator X H) - 1 ∈ algebra (X := X) (H := H) := by
  have hF' : F ^ 2 - 1 ∈ multiplierRoeIdeal (X := X) (H := H) := by
    rw [mem_multiplierRoeIdeal]
    simpa using hdefect
  have h := Analytic.rationalBoundaryUnitary_sub_one_mem
    (multiplierRoeIdeal (X := X) (H := H)) F hF hF'
  rw [mem_multiplierRoeIdeal] at h
  exact h

end CoarseAssembly.DiscreteRoe

end

end OAI
