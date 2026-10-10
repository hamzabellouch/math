import Mathlib

namespace OAI

namespace HarmonicArtin.LinearLayers

variable {K V₀ V₁ V₂ : Type*} [Field K]
  [AddCommGroup V₀] [Module K V₀]
  [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]

def differential (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂) (a : V₀ →ₗ[K] V₂) :
    (V₀ × V₁ × V₂) →ₗ[K] (V₀ × V₁ × V₂) where
  toFun x := (0, f x.1, a x.1 + g x.2.1)
  map_add' x y := by simp [add_assoc, add_left_comm, add_comm]
  map_smul' k x := by simp

@[simp] theorem differential_apply (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂)
    (a : V₀ →ₗ[K] V₂) (x : V₀ × V₁ × V₂) :
    differential f g a x = (0, f x.1, a x.1 + g x.2.1) := rfl

theorem differential_squared (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂)
    (a : V₀ →ₗ[K] V₂) (h : g.comp f = 0) :
    (differential f g a).comp (differential f g a) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : g (f x.1) = 0 := LinearMap.congr_fun h x.1
  simp [LinearMap.comp_apply, hx]

theorem middle_exact_of_identity_token
    (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂) (a : V₀ →ₗ[K] V₂)
    (idCycle : V₀ × V₁ × V₂) (token : V₂) (hid : idCycle.1 ≠ 0)
    (span_cycles : ∀ c, differential f g a c = 0 →
      ∃ k l : K, ∃ b, c = k • idCycle + l • (0, 0, token) + differential f g a b) :
    LinearMap.ker g ≤ LinearMap.range f := by
  intro y hy
  have hc : differential f g a (0, y, 0) = 0 := by
    simp [LinearMap.mem_ker.mp hy]
  obtain ⟨k, l, b, hb⟩ := span_cycles (0, y, 0) hc
  have hk : k = 0 := by
    have he := congrArg Prod.fst hb
    have he' : k • idCycle.1 = 0 := by simpa using he.symm
    exact (smul_eq_zero.mp he').resolve_right hid
  refine ⟨b.1, ?_⟩
  have he := congrArg (fun x : V₀ × V₁ × V₂ => x.2.1) hb
  simpa [hk] using he.symm

def secondary (g : V₁ →ₗ[K] V₂) (a : V₀ →ₗ[K] V₂) (U : Submodule K V₀) :
    U →ₗ[K] V₂ ⧸ LinearMap.range g :=
  (LinearMap.range g).mkQ.comp (a.comp U.subtype)

theorem secondary_injective
    (f : V₀ →ₗ[K] V₁) (g : V₁ →ₗ[K] V₂) (a : V₀ →ₗ[K] V₂)
    (idCycle : V₀ × V₁ × V₂) (token : V₂)
    (span_cycles : ∀ c, differential f g a c = 0 →
      ∃ k l : K, ∃ b, c = k • idCycle + l • (0, 0, token) + differential f g a b)
    (U : Submodule K V₀) (hU : U ≤ LinearMap.ker f)
    (hdisjoint : Disjoint U (Submodule.span K {idCycle.1})) :
    Function.Injective (secondary g a U) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hax : a x ∈ LinearMap.range g := by
    have hz : (LinearMap.range g).mkQ (a x) = 0 := hx
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨y, hy⟩ := hax
  have hc : differential f g a (x, -y, 0) = 0 := by
    have hfx : f x = 0 := hU x.property
    simp [hfx, ← hy]
  obtain ⟨k, l, b, hb⟩ := span_cycles (x, -y, 0) hc
  have he : (x : V₀) = k • idCycle.1 := by
    have he := congrArg Prod.fst hb
    simpa using he
  have hxspan : (x : V₀) ∈ Submodule.span K {idCycle.1} := by
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hxzero : (x : V₀) = 0 :=
    (Submodule.disjoint_def.mp hdisjoint) _ x.property hxspan
  exact Subtype.ext hxzero

end HarmonicArtin.LinearLayers

end OAI
