import OAI.Topology.CoarseAssembly.RoeIdealizer
import Mathlib.RingTheory.TwoSidedIdeal.Basic

namespace OAI

/-! # The Roe ideal and the algebraic analytic-index quotient

This is the actual two-sided ideal in the controlled pseudolocal algebra.
The quotient norm and the analytic-index class are constructed separately.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

def roeIdeal : TwoSidedIdeal (structureAlgebra (X := X) (H := H)) :=
  TwoSidedIdeal.mk' {T | T.val ∈ algebra (X := X) (H := H)}
    (algebra (X := X) (H := H)).zero_mem
    (fun hT hS => (algebra (X := X) (H := H)).add_mem hT hS)
    (fun hT => (algebra (X := X) (H := H)).neg_mem hT)
    (fun {T S} hS => (structureAlgebra_multiplier finiteBalls T.property) ⟨S.val, hS⟩ |>.1)
    (fun {T S} hT => (structureAlgebra_multiplier finiteBalls S.property) ⟨T.val, hT⟩ |>.2)

@[simp] theorem mem_roeIdeal (T : structureAlgebra (X := X) (H := H)) :
    T ∈ roeIdeal (H := H) finiteBalls ↔ T.val ∈ algebra (X := X) (H := H) := by
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

theorem roeIdeal_closed :
    IsClosed (roeIdeal (H := H) finiteBalls : Set (structureAlgebra (X := X) (H := H))) := by
  have he : (roeIdeal (H := H) finiteBalls : Set (structureAlgebra (X := X) (H := H))) =
      Subtype.val ⁻¹' (algebra (X := X) (H := H) : Set (Operator X H)) := by
    ext T
    exact mem_roeIdeal finiteBalls T
  rw [he]
  exact algebra_isClosed.preimage continuous_subtype_val

abbrev StructureQuotient := (roeIdeal (H := H) finiteBalls).ringCon.Quotient

def structureQuotientMap : structureAlgebra (X := X) (H := H) →ₙ+*
    StructureQuotient (H := H) finiteBalls where
  toFun T := (T : (roeIdeal (H := H) finiteBalls).ringCon.Quotient)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem structureQuotientMap_eq (T S : structureAlgebra (X := X) (H := H)) :
    structureQuotientMap (H := H) finiteBalls T = structureQuotientMap (H := H) finiteBalls S ↔
      T.val - S.val ∈ algebra (X := X) (H := H) := by
  change (T : (roeIdeal (H := H) finiteBalls).ringCon.Quotient) =
    (S : (roeIdeal (H := H) finiteBalls).ringCon.Quotient) ↔ _
  rw [RingCon.eq]
  exact (TwoSidedIdeal.rel_iff _ T S).trans (mem_roeIdeal finiteBalls (T - S))

end CoarseAssembly.DiscreteRoe

end

end OAI
