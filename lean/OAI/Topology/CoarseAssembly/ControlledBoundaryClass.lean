import OAI.Topology.CoarseAssembly.CayleyBoundary
import OAI.Topology.CoarseAssembly.RelativeUnitary
import OAI.Topology.CoarseAssembly.UnitalStructureAlgebra

namespace OAI

/-! # The K₁ boundary representative of a controlled Fredholm operator

The operator, its self-adjointness, and its Roe square defect are concrete
data. Localization of arbitrary Fredholm cycles and descent through their
relations are separate obligations of the assembly construction.
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

variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

def unitalRoeIdeal : TwoSidedIdeal (unitalStructureAlgebra (X := X) (H := H)) :=
  TwoSidedIdeal.mk' {T | T.val ∈ algebra (X := X) (H := H)}
    (algebra (X := X) (H := H)).zero_mem
    (fun hT hS => (algebra (X := X) (H := H)).add_mem hT hS)
    (fun hT => (algebra (X := X) (H := H)).neg_mem hT)
    (fun {T S} hS => (structureAlgebra_multiplier finiteBalls T.property) ⟨S.val, hS⟩ |>.1)
    (fun {T S} hT => (structureAlgebra_multiplier finiteBalls S.property) ⟨T.val, hT⟩ |>.2)

@[simp] theorem mem_unitalRoeIdeal (T : unitalStructureAlgebra (X := X) (H := H)) :
    T ∈ unitalRoeIdeal (H := H) finiteBalls ↔ T.val ∈ algebra (X := X) (H := H) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

def controlledBoundaryUnitary (F : unitalStructureAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) : unitary (Operator X H) :=
  Unitary.map (StarMonoidHom.ofClass (unitalStructureAlgebra (X := X) (H := H)).subtype)
    (Analytic.rationalBoundaryUnitary F hF)

include finiteBalls in
theorem controlledBoundaryUnitary_sub_one_mem
    (F : unitalStructureAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    (controlledBoundaryUnitary F hF : Operator X H) - 1 ∈ algebra (X := X) (H := H) := by
  have hF' : F ^ 2 - 1 ∈ unitalRoeIdeal (H := H) finiteBalls := by
    rw [mem_unitalRoeIdeal]
    simpa using hdefect
  have h := Analytic.rationalBoundaryUnitary_sub_one_mem
    (unitalRoeIdeal (H := H) finiteBalls) F hF hF'
  rw [mem_unitalRoeIdeal] at h
  exact h

/-- An actual class of the reduced locally compact Roe algebra. -/
def controlledBoundaryClass
    (F : unitalStructureAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    OperatorKTheory.K1 (algebra (X := X) (H := H)) :=
  OperatorKTheory.relativeClass (hS := algebra_isClosed) (algebra (X := X) (H := H))
    (controlledBoundaryUnitary F hF)
    (controlledBoundaryUnitary_sub_one_mem finiteBalls F hF hdefect)

theorem controlledBoundaryClass_of_involution
    (F : unitalStructureAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) (hsq : F ^ 2 = 1) :
    controlledBoundaryClass finiteBalls F hF hdefect = 0 := by
  apply OperatorKTheory.relativeClass_eq_zero (hS := algebra_isClosed)
  apply Subtype.ext
  change ((Analytic.rationalBoundaryUnitary F hF :
    unitalStructureAlgebra (X := X) (H := H)) : Operator X H) = 1
  rw [Analytic.rationalBoundaryUnitary_eq_one F hF hsq]
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
