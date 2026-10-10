import OAI.Topology.CoarseAssembly.ProjectionBlocks
import OAI.Topology.CoarseAssembly.ConcreteTransfer

namespace OAI

/-! # Uniform spatial approximation from the published gap

The gap hypothesis is the norm estimate for the explicitly defined lazy
regular-representation averages. The direct-sum convergence and its
identification with the actual spatial constant-fiber projection are proved
here, as required by the transfer construction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence DiscreteRoe
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The precise uniform operator consequence of the Kazhdan estimate for
the chosen generators, on the coefficient Hilbert space used by the Roe
module. For the standard generators this is the specialization of BHV,
Proposition 1.3.2 and Example 1.7.4, described in manuscript §5.2. -/
def UniformAveragingGap (S : Finset ArithmeticGroup) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ k,
    ‖lazyAverage (H := H) S k - constantProjection (H := H) (Quotient k)‖ ≤ c

theorem fiberAveragingPower_norm (S : Finset ArithmeticGroup) (n : ℕ) (u : BaseUnion) :
    ‖lazyAverage (H := H) S (discDepth u.1 u.2) ^ (n + 1)‖ ≤ 1 := by
  calc
    _ ≤ ‖lazyAverage (H := H) S (discDepth u.1 u.2)‖ ^ (n + 1) :=
      norm_pow_le' _ (Nat.succ_pos n)
    _ ≤ 1 ^ (n + 1) := by gcongr; exact lazyAverage_norm_le S _
    _ = 1 := one_pow _

def spatialAveragingPower (S : Finset ArithmeticGroup) (n : ℕ) : Operator VertexUnion H :=
  flattenOperator (Q := BaseFiber) (blockOperator
    (fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2) ^ (n + 1))
    1 zero_le_one (fiberAveragingPower_norm (H := H) S n))

theorem spatialAveragingPower_tendsto (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (hgap : UniformAveragingGap S H) :
    Filter.Tendsto (spatialAveragingPower (H := H) S) Filter.atTop
      (nhds (fiberProjection (H := H) BaseFiber)) := by
  obtain ⟨c, hc, hc1, hgap⟩ := hgap
  let M := fun u : BaseUnion => lazyAverage (H := H) S (discDepth u.1 u.2)
  let P := fun u : BaseUnion => constantProjection (H := H) (BaseFiber u)
  have hM (u : BaseUnion) : ‖M u‖ ≤ 1 := lazyAverage_norm_le S _
  have hP (u : BaseUnion) : ‖P u‖ ≤ 1 := constantProjection_norm_le _
  have hconv := averaging_blocks_tendsto
    (ι := BaseUnion) (E := fun u => lp (fun _ : BaseFiber u => H) 2)
    M P c hc hc1 hM hP
    (fun u => constantProjection_idempotent (H := H) (BaseFiber u))
    (fun u => lazyAverage_projection (H := H) S hS (discDepth u.1 u.2))
    (fun u => projection_lazyAverage (H := H) S hS (discDepth u.1 u.2))
    (fun u => hgap (discDepth u.1 u.2))
  have hflat := flattenOperator_tendsto (Q := BaseFiber) (H := H) _ _ hconv
  rw [flatten_constantProjection (Q := BaseFiber) (H := H)] at hflat
  exact hflat

end CoarseAssembly

end

end OAI
