import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ModuleSequence
universe u v w w' w'' z z' z''
variable {A : Type u} [CommRing A]
  {M : Type v} {N : Type w} {P : Type w'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P]

lemma transport {M' : Type z} {N' : Type z'} {P' : Type z''}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module A M'] [Module A N'] [Module A P']
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (f' : M' →ₗ[A] N') (g' : N' →ₗ[A] P')
    (eM : M ≃ₗ[A] M') (eN : N ≃ₗ[A] N') (eP : P ≃ₗ[A] P')
    (hf : eN.toLinearMap.comp f=f'.comp eM.toLinearMap)
    (hg : eP.toLinearMap.comp g=g'.comp eN.toLinearMap)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g' := by
  have hf' (x : M) : eN (f x)=f' (eM x) := DFunLike.congr_fun hf x
  have hg' (x : N) : eP (g x)=g' (eN x) := DFunLike.congr_fun hg x
  refine ⟨?_,?_,?_⟩
  · intro x y h
    obtain ⟨x,rfl⟩ := eM.surjective x
    obtain ⟨y,rfl⟩ := eM.surjective y
    apply congrArg eM
    apply hi
    apply eN.injective
    rw [hf',hf']
    exact h
  · exact (Function.Exact.iff_of_ladder_linearEquiv hf.symm hg.symm).mpr he
  · intro y
    obtain ⟨y,rfl⟩ := eP.surjective y
    obtain ⟨x,rfl⟩ := hs y
    exact ⟨eN x,(hg' x).symm⟩

lemma baseChange (B : Type z) [CommRing B] [Algebra A B] [Module.Flat A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hi : Function.Injective f) (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Injective (f.baseChange B) ∧ Function.Exact (f.baseChange B) (g.baseChange B) ∧
      Function.Surjective (g.baseChange B) :=
  ⟨LinearMap.lTensor_injective_of_exact_of_flat g hs f hi he B,
    lTensor_exact B he hs,LinearMap.lTensor_surjective B hs⟩
end Lech.ModuleSequence

end

end OAI
