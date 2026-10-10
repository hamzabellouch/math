import Mathlib

namespace OAI

namespace HarmonicArtin.LinearLayers

open Module

variable {K V₀ V₁ V₂ W₀ W₁ : Type*} [Field K]
  [AddCommGroup V₀] [Module K V₀]
  [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup W₀] [Module K W₀]
  [AddCommGroup W₁] [Module K W₁]

abbrev Middle (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂) :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

theorem range_le_ker_of_comp_zero (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂)
    (h : g.comp f = 0) : LinearMap.range f ≤ LinearMap.ker g := by
  rintro _ ⟨x, rfl⟩
  exact LinearMap.congr_fun h x

theorem three_column_euler [FiniteDimensional K V₀] [FiniteDimensional K V₁]
    [FiniteDimensional K V₂] (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂)
    (h : g.comp f = 0) :
    finrank K V₀ + finrank K V₂ + finrank K (Middle f g) =
      finrank K V₁ + finrank K (LinearMap.ker f) +
        finrank K (V₂ ⧸ LinearMap.range g) := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hq := (LinearMap.range g).finrank_quotient_add_finrank
  have hm := ((LinearMap.range f).comap (LinearMap.ker g).subtype).finrank_quotient_add_finrank
  have he := (Submodule.comapSubtypeEquivOfLe (range_le_ker_of_comp_zero f g h)).finrank_eq
  change finrank K (Middle f g) +
    finrank K ((LinearMap.range f).comap (LinearMap.ker g).subtype) =
      finrank K (LinearMap.ker g) at hm
  omega

theorem rank_eq_of_adjoint (g : V₁ →ₗ[K] V₂) (f : W₀ →ₗ[K] W₁)
    (e₀ : W₀ ≃ₗ[K] Module.Dual K V₂) (e₁ : W₁ ≃ₗ[K] Module.Dual K V₁)
    (h : e₁.toLinearMap.comp f = g.dualMap.comp e₀.toLinearMap) :
    finrank K (LinearMap.range f) = finrank K (LinearMap.range g) := by
  have hr := congrArg (fun l : W₀ →ₗ[K] Module.Dual K V₁ =>
    finrank K (LinearMap.range l)) h
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top] at hr
  rw [e₁.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range] at hr
  exact hr

theorem kernel_cokernel_dimension [FiniteDimensional K V₂] [FiniteDimensional K W₀]
    (g : V₁ →ₗ[K] V₂) (f : W₀ →ₗ[K] W₁)
    (e₀ : W₀ ≃ₗ[K] Module.Dual K V₂) (e₁ : W₁ ≃ₗ[K] Module.Dual K V₁)
    (h : e₁.toLinearMap.comp f = g.dualMap.comp e₀.toLinearMap) :
    finrank K (LinearMap.ker f) = finrank K (V₂ ⧸ LinearMap.range g) := by
  have hf := f.finrank_range_add_finrank_ker
  have hq := (LinearMap.range g).finrank_quotient_add_finrank
  have hr := rank_eq_of_adjoint g f e₀ e₁ h
  have he : finrank K W₀ = finrank K V₂ :=
    e₀.finrank_eq.trans (Subspace.dual_finrank_eq)
  omega

theorem paired_euler [FiniteDimensional K V₀] [FiniteDimensional K V₁]
    [FiniteDimensional K V₂] [FiniteDimensional K W₀]
    (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂) (hgf : g.comp f = 0)
    (f' : W₀ →ₗ[K] W₁)
    (e₀ : W₀ ≃ₗ[K] Module.Dual K V₂) (e₁ : W₁ ≃ₗ[K] Module.Dual K V₁)
    (hadj : e₁.toLinearMap.comp f' = g.dualMap.comp e₀.toLinearMap) :
    finrank K V₀ + finrank K V₂ + finrank K (Middle f g) =
      finrank K V₁ + finrank K (LinearMap.ker f) + finrank K (LinearMap.ker f') := by
  rw [kernel_cokernel_dimension g f' e₀ e₁ hadj]
  exact three_column_euler f g hgf

end HarmonicArtin.LinearLayers

end OAI
