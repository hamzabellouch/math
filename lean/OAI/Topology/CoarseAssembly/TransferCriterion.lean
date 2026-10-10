import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.TensorFibers
import OAI.Topology.CoarseAssembly.TransferLift
import OAI.Topology.CoarseAssembly.RoeTransfer

namespace OAI

/-! # The finite-fiber Roe transfer criterion

This proves the operator statement of Proposition 5.1. The required
finite-propagation scalar contractions between fibers are amplified here;
the bounded lift, compactness and compression are constructed, not assumed.
The concrete graph family still has to supply these fiber contractions and
the averaging approximants.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe
open scoped Topology

variable {D : Type*} [DecidableEq D] [PseudoMetricSpace D]

variable {Q : D → Type*} [∀ u, Fintype (Q u)] [∀ u, Nonempty (Q u)]
variable [∀ u, DecidableEq (Q u)] [PseudoMetricSpace (Sigma Q)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform controlled scalar maps preserving the normalized constants. -/
def ControlledFiberMaps (Q : D → Type*) [∀ u, Fintype (Q u)]
    [∀ u, DecidableEq (Q u)] [PseudoMetricSpace (Sigma Q)] : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ s : ℝ, 0 ≤ s ∧
    ∃ O : ∀ u v, lp (fun _ : Q v => ℂ) 2 →L[ℂ] lp (fun _ : Q u => ℂ) 2,
      ∀ u v, dist u v ≤ R →
        ‖O u v‖ ≤ 1 ∧ O u v (fiberConstant (Q v) (1 : ℂ)) = fiberConstant (Q u) 1 ∧
        ∀ q r, s < dist (⟨u, q⟩ : Sigma Q) ⟨v, r⟩ → O u v (lp.single 2 r 1) q = 0

theorem lift_generator_from_fiber_maps (hD : UniformFiniteBalls D)
    (hO : ControlledFiberMaps Q) (T : Operator D H) (hT : Generator T) :
    ∃ A : Operator (Sigma Q) H, Generator A ∧
      fiberProjection Q * A * fiberProjection Q = operatorConjugation (fiberEmbedding Q) T := by
  obtain ⟨R, hR, hpropT⟩ := hT.1
  obtain ⟨N, hballs⟩ := hD R hR
  let rows : D → Finset D := fun u => (hballs u).choose
  have hmem (u v : D) : v ∈ rows u ↔ dist u v ≤ R := (hballs u).choose_spec.1 v
  have hcard (u : D) : (rows u).card ≤ N := (hballs u).choose_spec.2
  have hdual (u v : D) : v ∈ rows u ↔ u ∈ rows v := by
    rw [hmem, hmem, dist_comm]
  obtain ⟨s, hs, O, hO⟩ := hO R hR
  let B := fun u v => amplifyFiber (O u v) (entry T u v)
  have hB (u v : D) (huv : v ∈ rows u) : ‖B u v‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖O u v‖ * ‖entry T u v‖ := amplifyFiber_norm_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul (hO u v ((hmem u v).mp huv)).1
        (entry_norm_le T u v) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  let A := spatialBlocks rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB
  refine ⟨A, ?_, ?_⟩
  · apply spatialBlocks_generator rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB T hT s hs
    · intro u v huv q r hdist
      apply ContinuousLinearMap.ext
      intro h
      change amplifyFiber (O u v) (entry T u v) (lp.single 2 r h) q = 0
      rw [amplifyFiber_single, (hO u v ((hmem u v).mp huv)).2.2 q r hdist, zero_smul]
    · intro u v huv q r
      refine ⟨O u v (lp.single 2 r 1) q, ?_⟩
      apply ContinuousLinearMap.ext
      intro h
      exact amplifyFiber_single (O u v) (entry T u v) r q h
  · apply spatialBlocks_compression rows rows hdual B N ‖T‖ (norm_nonneg T) hcard hcard hB T
    · intro u v huv
      exact hpropT u v (lt_of_not_ge (fun h => huv ((hmem u v).mpr h)))
    · intro u v huv h
      exact amplifyFiber_constant (O u v) (entry T u v)
        (hO u v ((hmem u v).mp huv)).2.1 h

/-- The finite-fiber transfer lands in the ordinary locally compact reduced
Roe algebra. The approximation is an operator-norm approximation of the
amplified projection; the projection itself need not be locally compact. -/
theorem finite_fiber_transfer (hD : UniformFiniteBalls D)
    (hX : ∀ x : Sigma Q, ∀ r : ℝ, (Metric.closedBall x r).Finite)
    (hO : ControlledFiberMaps Q)
    (Pn : ℕ → Operator (Sigma Q) H)
    (hlim : Filter.Tendsto Pn Filter.atTop (nhds (fiberProjection Q)))
    (hprop : ∀ n, ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r (Pn n)) :
    MapsToRoe (fiberEmbedding (H := H) Q) := by
  intro T hT
  apply conjugation_mem_of_sandwich_lifts hX (fiberEmbedding Q) (fiberProjection Q) Pn hlim hprop
    (fun T hT => lift_generator_from_fiber_maps hD hO T hT) hT

end CoarseAssembly

end

end OAI
