import OAI.Topology.CoarseAssembly.UniformSubdivision
import OAI.Topology.CoarseAssembly.RipsLocalization

namespace OAI

/-! # Simultaneous finite subdivision of the operator and partition coordinates -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

theorem exists_rips_homotopy_subdivision (r : ℝ) (h : OddHomotopy C(Point X r, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ j, j < N →
      ‖h.operator (intervalGrid N hN (j + 1)) - h.operator (intervalGrid N hN j)‖ ≤ ε ∧
      ∀ x, ‖h.representation (intervalGrid N hN (j + 1)) (sqrtCoordinate r x) -
        h.representation (intervalGrid N hN j) (sqrtCoordinate r x)‖ ≤ ε := by
  let f : Interval → End h.space × (X → End h.space) :=
    fun t => (h.operator t, fun x => h.representation t (sqrtCoordinate r x))
  have hf : Continuous f := h.continuous_operator.prodMk
    (continuous_pi (fun x => h.continuous_representation (sqrtCoordinate r x)))
  obtain ⟨N, hN, hstep⟩ := exists_interval_subdivision f hf ε hε
  refine ⟨N, hN, fun j hj => ?_⟩
  have he : ‖f (intervalGrid N hN (j + 1)) - f (intervalGrid N hN j)‖ ≤ ε := by
    simpa only [dist_eq_norm] using (hstep j hj).le
  refine ⟨(norm_fst_le _).trans he, fun x => ?_⟩
  exact (norm_le_pi_norm _ x).trans ((norm_snd_le _).trans he)

end CoarseAssembly.Rips

end

end OAI
