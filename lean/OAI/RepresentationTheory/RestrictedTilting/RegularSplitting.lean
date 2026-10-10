import Mathlib

namespace OAI

namespace FiberFunctorProof
open Representation
universe u v
variable {k : Type u} [Field k] {G : Type v} [Group G] [Fintype G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

lemma intertwining_norm {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (v : V) : f (ρ.norm v) = σ.norm (f v) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum, f.isIntertwining]

noncomputable def regularCoefficients : MonoidAlgebra k G ≃ₗ[k] (G → k) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans (Finsupp.linearEquivFunOnFinite k k G)

omit [Group G] in
@[simp] lemma regularCoefficients_apply (x : MonoidAlgebra k G) (g : G) :
    regularCoefficients x g = x.coeff g := rfl

omit [Group G] in
@[simp] lemma regularCoefficients_symm_coeff (v : G → k) (g : G) :
    (regularCoefficients.symm v).coeff g = v g := by
  exact congrFun (regularCoefficients.apply_symm_apply v) g

 

noncomputable def regularCofree (ρ : Representation k G V) (φ : V →ₗ[k] k) :
    ρ.IntertwiningMap (Representation.leftRegular k G) where
  toLinearMap := regularCoefficients.symm.toLinearMap.comp
    (LinearMap.pi fun g : G => φ.comp (ρ g⁻¹))
  isIntertwining' h := by
    ext v g
    simp [regularCoefficients_symm_coeff, Representation.coeff_ofMulAction,
      mul_inv_rev, map_mul]

@[simp] lemma regularCofree_coeff (ρ : Representation k G V) (φ : V →ₗ[k] k)
    (v : V) (g : G) : (regularCofree ρ φ v).coeff g = φ (ρ g⁻¹ v) := by
  exact regularCoefficients_symm_coeff _ g

 

theorem regular_split_of_injective (ρ : Representation k G V)
    (f : (Representation.leftRegular k G).IntertwiningMap ρ)
    (hf : Function.Injective f) :
    ∃ s : ρ.IntertwiningMap (Representation.leftRegular k G),
      s.comp f = Representation.IntertwiningMap.id _ := by
  obtain ⟨j,hj⟩ := f.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  have hji (x : MonoidAlgebra k G) : j (f x) = x := congr($(hj) x)
  let φ : V →ₗ[k] k := (Finsupp.lapply 1).comp
    ((MonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp j)
  refine ⟨regularCofree ρ φ, ?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  change (regularCofree ρ φ (f x)).coeff g = x.coeff g
  rw [regularCofree_coeff, ← f.isIntertwining]
  change (j (f ((Representation.leftRegular k G) g⁻¹ x))).coeff 1 = x.coeff g
  rw [hji]
  simp [Representation.coeff_ofMulAction]

lemma regular_norm_single_coeff (g : G) :
    ((Representation.leftRegular k G).norm (MonoidAlgebra.single 1 1)).coeff g = 1 := by
  classical
  simp [Representation.norm]

 
theorem regular_invariant_eq (x : MonoidAlgebra k G)
    (hx : ∀ g, (Representation.leftRegular k G) g x = x) :
    x = x.coeff 1 • (Representation.leftRegular k G).norm (MonoidAlgebra.single 1 1) := by
  ext g
  have h := congrArg (fun a : MonoidAlgebra k G => a.coeff g) (hx g)
  simp [Representation.coeff_ofMulAction] at h
  simpa [regular_norm_single_coeff] using h.symm
end FiberFunctorProof

end OAI
