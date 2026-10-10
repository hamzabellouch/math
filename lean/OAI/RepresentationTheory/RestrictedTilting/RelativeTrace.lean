import Mathlib

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u v
variable {k : Type u} [Field k] {G : Type v} [Group G] [Fintype G]
variable {V W U : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

 
noncomputable def relativeTrace (ρ : Representation k G V) (σ : Representation k G W) :
    (V →ₗ[k] W) →ₗ[k] (V →ₗ[k] W) := (Representation.linHom ρ σ).norm

lemma relativeTrace_apply (ρ : Representation k G V) (σ : Representation k G W)
    (t : V →ₗ[k] W) (v : V) :
    relativeTrace ρ σ t v = ∑ g : G, σ g (t (ρ g⁻¹ v)) := by
  simp [relativeTrace, Representation.norm, LinearMap.sum_apply]

noncomputable def relativeTraceHom (ρ : Representation k G V) (σ : Representation k G W)
    (t : V →ₗ[k] W) : ρ.IntertwiningMap σ where
  toLinearMap := relativeTrace ρ σ t
  isIntertwining' g := by
    have h := (Representation.linHom ρ σ).self_norm_apply g t
    have hh := congrArg (fun f : V →ₗ[k] W => f.comp (ρ g)) h
    simpa only [Representation.linHom_apply, LinearMap.comp_assoc,
      ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id, relativeTrace]
      using hh.symm

lemma relativeTrace_precomp (ρ : Representation k G V) (σ : Representation k G W)
    (τ : Representation k G U) (a : ρ.IntertwiningMap σ) (t : W →ₗ[k] U) :
    relativeTrace ρ τ (t.comp a.toLinearMap) =
      (relativeTrace σ τ t).comp a.toLinearMap := by
  ext v
  simp only [relativeTrace_apply, LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
    a.isIntertwining]

lemma relativeTrace_postcomp (ρ : Representation k G V) (σ : Representation k G W)
    (τ : Representation k G U) (b : σ.IntertwiningMap τ) (t : V →ₗ[k] W) :
    relativeTrace ρ τ (b.toLinearMap.comp t) =
      b.toLinearMap.comp (relativeTrace ρ σ t) := by
  ext v
  simp only [relativeTrace_apply, LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
    map_sum, b.isIntertwining]

end FiberFunctorProof

end OAI
