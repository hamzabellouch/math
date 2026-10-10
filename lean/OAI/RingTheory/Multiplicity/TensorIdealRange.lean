import Mathlib

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (a : ℕ) (hf : f.range = I^a • (⊤ : Submodule R N))
  (Q : Type u) [AddCommGroup Q] [Module R Q]

include hf in
lemma range_lTensor : (f.lTensor Q).range = I^a • (⊤ : Submodule R (Q ⊗[R] N)) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
        change x ⊗ₜ[R] f y ∈ _
        have hy : f y ∈ I^a • (⊤ : Submodule R N) := hf ▸ LinearMap.mem_range_self f y
        refine Submodule.smul_induction_on hy (fun r hr y hy => ?_) (fun y z hy hz => ?_)
        · rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hy hz
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro r hr x _
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
        have hy : r • y ∈ f.range := hf ▸ Submodule.smul_mem_smul hr Submodule.mem_top
        obtain ⟨z,hz⟩ := hy
        refine ⟨x ⊗ₜ[R] z,?_⟩
        rw [LinearMap.lTensor_tmul,hz,TensorProduct.tmul_smul]
    | add x y hx hy => rw [smul_add]; exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

 

def equiv [Module.Flat R Q] (hinj : Function.Injective f) :
    (Q ⊗[R] M) ≃ₗ[R] ↥(I^a • (⊤ : Submodule R (Q ⊗[R] N))) :=
  (LinearEquiv.ofInjective (f.lTensor Q)
    (Module.Flat.lTensor_preserves_injective_linearMap f hinj)).trans
      (LinearEquiv.ofEq _ _ (range_lTensor I f a hf Q))

lemma equiv_val [Module.Flat R Q] (hinj : Function.Injective f) (x : Q ⊗[R] M) :
    (equiv I f a hf Q hinj x).val = f.lTensor Q x := rfl
end Lech.TensorIdeal

end

end OAI
