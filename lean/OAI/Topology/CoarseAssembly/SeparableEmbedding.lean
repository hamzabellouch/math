import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FredholmModule
import OAI.Topology.CoarseAssembly.InclusionModule
import Mathlib.Topology.Bases

namespace OAI

/-! # Placing each separable cycle on the fixed ample coefficient space -/

noncomputable section

namespace CoarseAssembly.Analytic

theorem orthonormal_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [SecondCountableTopology H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 2 : ℝ))
      (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hn : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ]
      norm_num [hv.norm_eq_one, hv.inner_eq_zero hij]
    have hzi' : dist (v i) z < 1 / 2 := by simpa only [Metric.mem_ball, dist_comm] using hzi
    have hzj' : dist z (v j) < 1 / 2 := hzj
    have hdist : dist (v i) (v j) < 1 := by linarith [dist_triangle (v i) z (v j)]
    rw [dist_eq_norm] at hdist
    nlinarith [norm_nonneg (v i - v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- Only an isometric embedding is needed; the orthogonal complement is
handled by the identity extension of the Fredholm operator. -/
theorem exists_ampleIsometry (H : HilbertSpace) :
    Nonempty (H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ H
  let : Countable s := orthonormal_countable b.orthonormal
  obtain ⟨f, hf⟩ := exists_injective_nat s
  exact ⟨(inclusionIsometry (H := ℂ) ⟨f, hf⟩).comp b.repr.toLinearIsometry⟩

end CoarseAssembly.Analytic

end

end OAI
