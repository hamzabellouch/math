import OAI.Topology.CoarseAssembly.CompactBlockSum
import OAI.Topology.CoarseAssembly.CountableAdditivity

namespace OAI

/-! # Decay of compact-component norms for functions vanishing at infinity -/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology Filter
open scoped ZeroAtInfty

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]

def sigmaFunctionRestriction (j : ℕ) : C₀(Sigma Y, ℂ) →⋆ₙₐ[ℂ] C(Y j, ℂ) where
  toFun f := ⟨fun x => f ⟨j, x⟩, f.continuous.comp continuous_sigmaMk⟩
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  map_star' _ := by ext x; rfl

omit [∀ j, CompactSpace (Y j)] in
@[simp] theorem sigmaFunctionRestriction_apply (j : ℕ) (f : C₀(Sigma Y, ℂ)) (x : Y j) :
    sigmaFunctionRestriction Y j f x = f ⟨j, x⟩ := rfl

theorem sigmaFunctionRestriction_norm_le (j : ℕ) (f : C₀(Sigma Y, ℂ)) :
    ‖sigmaFunctionRestriction Y j f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact f.toBCF.norm_coe_le_norm ⟨j, x⟩

theorem sigmaFunctionRestriction_norm_tendsto (f : C₀(Sigma Y, ℂ)) :
    Tendsto (fun j => ‖sigmaFunctionRestriction Y j f‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : {x : Sigma Y | dist (f x) 0 < ε / 2} ∈ cocompact (Sigma Y) :=
    Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (by positivity)
  obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp hsmall
  obtain ⟨s, t, hs, _ht, hKs⟩ := hK.sigma_exists_finite_sigma_eq
  obtain ⟨N, hN⟩ := hs.bddAbove
  refine ⟨N + 1, fun j hj => ?_⟩
  have hjout : j ∉ s := by
    intro hjs
    have := hN hjs
    omega
  have hnorm : ‖sigmaFunctionRestriction Y j f‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ε / 2)).mpr
    intro x
    have hxout : (⟨j, x⟩ : Sigma Y) ∉ K := by
      rw [← hKs]
      intro hx
      exact hjout hx.1
    have h := hbound hxout
    change dist (f ⟨j, x⟩) 0 < ε / 2 at h
    simpa only [sigmaFunctionRestriction_apply, dist_zero_right] using h.le
  rw [dist_zero_right, norm_norm]
  exact hnorm.trans_lt (by linarith)

end CoarseAssembly.Analytic

end

end OAI
