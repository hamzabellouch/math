import Mathlib
import OAI.RingTheory.Multiplicity.TorsionZeroStability

namespace OAI

noncomputable section
namespace Lech.TorsionLength
open CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)
  {A M N : Type u} [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

omit [Module R N] [IsScalarTower R A N] in
lemma tensor_torsion_left (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (M ⊗[A] N)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
      rw [TensorProduct.smul_tmul',Module.mem_annihilator.mp (ha hr) m,TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add,hx,hy,add_zero]

omit [Module R N] [IsScalarTower R A N] in
lemma tensor_zero_left_torsion (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R M)) (hM : ell.value (ModuleCat.of R M)=0) :
    ell.value (ModuleCat.of R (M ⊗[A] N))=0 := by
  let f (n : N) : M →ₗ[R] M ⊗[A] N := ((TensorProduct.mk A M N).flip n).restrictScalars R
  apply ell.zero_of_ranges_torsion hds f (tensor_torsion_left hT) (fun _ => hT) (fun _ => hM)
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact (le_iSup (fun n => (f n).range) n) ⟨m,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

omit [Module R N] [IsScalarTower R A N] in
lemma rTensor_map_kernel_zero_torsion (hds : ell.DirectSumZero)
    {V : Type u} [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hTk : powerTorsion I (ModuleCat.of R f.ker))
    (hker : ell.value (ModuleCat.of R f.ker)=0) :
    ell.value (ModuleCat.of R (f.rTensor V).ker)=0 := by
  let k := f.ker.subtype.rTensor V
  have he := _root_.rTensor_exact V f.exact_subtype_ker_map hf
  let q : f.ker ⊗[A] V →ₗ[R] (f.rTensor V).ker :=
    (k.restrictScalars R).codRestrict ((f.rTensor V).ker.restrictScalars R) (fun x => by
      change (f.rTensor V) (k x)=0
      exact he.apply_apply_eq_zero x)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v,hv⟩ := he x.val |>.mp x.property
    exact ⟨v,Subtype.ext hv⟩
  exact ell.zero_of_surjective_torsion q hq (tensor_torsion_left hTk)
    (ell.tensor_zero_left_torsion hds hTk hker)
end Lech.TorsionLength

end

end OAI
