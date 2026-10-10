import Mathlib
import OAI.RingTheory.Multiplicity.TensorIdealRange

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  (I : Ideal R) (f : M →ₗ[A] N) (hf : Function.Surjective f)
  (hker : (f.restrictScalars R).ker = I • (⊤ : Submodule R M))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include hf hker in
lemma kernel_rTensor : ((f.rTensor V).restrictScalars R).ker =
    I • (⊤ : Submodule R (M ⊗[A] V)) := by
  have hex := _root_.rTensor_exact V f.exact_subtype_ker_map hf
  apply le_antisymm
  · intro x hx
    obtain ⟨y,rfl⟩ := hex x |>.mp hx
    clear hx
    induction y using TensorProduct.inductionOn with
    | tmul m v =>
        change m.val ⊗ₜ[A] v ∈ _
        have hm : m.val ∈ I • (⊤ : Submodule R M) := hker ▸ m.property
        refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) (fun m m' hm hm' => ?_)
        · rw [←TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · rw [TensorProduct.add_tmul]
          exact Submodule.add_mem _ hm hm'
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro r hr x _
    induction x using TensorProduct.inductionOn with
    | tmul m v =>
        rw [TensorProduct.smul_tmul']
        change f (r • m) ⊗ₜ[A] v=0
        have hm : r • m ∈ (f.restrictScalars R).ker :=
          hker ▸ Submodule.smul_mem_smul hr Submodule.mem_top
        have hfm : f (r • m)=0 := LinearMap.mem_ker.mp hm
        rw [hfm,TensorProduct.zero_tmul]
    | add x y hx hy => rw [smul_add]; exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

 
def quotientTensorEquiv :
    ((M ⊗[A] V) ⧸ (I • (⊤ : Submodule R (M ⊗[A] V)))) ≃ₗ[R] (N ⊗[A] V) :=
  (Submodule.quotEquivOfEq _ _ (kernel_rTensor I f hf hker V).symm).trans
    (LinearMap.quotKerEquivOfSurjective ((f.rTensor V).restrictScalars R)
      (LinearMap.rTensor_surjective V hf))

end Lech.TensorIdeal

end

end OAI
