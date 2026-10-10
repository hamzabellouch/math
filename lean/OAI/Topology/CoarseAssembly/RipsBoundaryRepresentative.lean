import OAI.Topology.CoarseAssembly.RipsLocalization
import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass
import OAI.Topology.CoarseAssembly.FiniteCompactRoe

namespace OAI

/-! # The actual boundary representative on a finite Rips component

This constructs the component operator and Roe K₁ class. No inference from
componentwise classes to the whole coarse disjoint union is made here.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X]
  (r : ℝ) (hr : 0 ≤ r)

def ripsMultiplier (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    multiplierAlgebra (X := X) (H := c.space) :=
  ⟨ripsSpatialOperator r c hπ,
    finitePropagation_multiplier (fun _ _ => Set.toFinite _) (add_nonneg hr hr)
      (ripsSpatialOperator_propagation r hr c hπ)⟩

theorem ripsMultiplier_selfAdjoint (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    IsSelfAdjoint (ripsMultiplier r hr c hπ) := by
  apply Subtype.ext
  exact (ripsSpatialOperator_selfAdjoint r c hπ hF).star_eq

theorem ripsSpatialOperator_square_mem_roe (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    (ripsSpatialOperator r c hπ) ^ 2 - 1 ∈ algebra (X := X) (H := c.space) := by
  apply compact_selfAdjoint_mem_roe
  · simpa only [pow_two] using ripsSpatialOperator_square_compact r c hπ hF
  · have hs : IsSelfAdjoint ((ripsSpatialOperator r c hπ) ^ 2 : Operator X c.space) :=
      (ripsSpatialOperator_selfAdjoint r c hπ hF).pow 2
    have hi : IsSelfAdjoint (1 : Operator X c.space) := IsSelfAdjoint.one _
    exact @IsSelfAdjoint.sub (Operator X c.space) inferInstance inferInstance _ _ hs hi

/-- The constructed boundary element, before passage to the fixed ample
module and before descent of the entire assembly homomorphism. -/
def ripsBoundaryRepresentative (c : OddCycle C(Point X r, ℂ))
    (hπ : c.representation 1 = 1) (hF : IsSelfAdjoint c.operator) :
    OperatorKTheory.K1 (algebra (X := X) (H := c.space)) :=
  multiplierBoundaryClass (ripsMultiplier r hr c hπ)
    (ripsMultiplier_selfAdjoint r hr c hπ hF)
    (ripsSpatialOperator_square_mem_roe r c hπ hF)

end CoarseAssembly.Rips

end

end OAI
