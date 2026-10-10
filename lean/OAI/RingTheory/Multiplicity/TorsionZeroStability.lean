import Mathlib
import OAI.RingTheory.Multiplicity.FiniteComplexTopInclusion

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

 
def TorsionLength.DirectSumZero (ell : TorsionLength I) : Prop :=
  ∀ {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (a : ℕ), (∀ i, I^a ≤ Module.annihilator R (M i)) →
      (∀ i, ell.value (ModuleCat.of R (M i))=0) → ell.value (ModuleCat.of R (⨁ i, M i))=0

namespace TorsionLength
variable (ell : TorsionLength I)

lemma zero_of_surjective_torsion {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hT : powerTorsion I (ModuleCat.of R M)) (hM : ell.value (ModuleCat.of R M)=0) :
    ell.value (ModuleCat.of R N)=0 := by
  let : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  exact le_antisymm ((ell.le_of_epi (ModuleCat.ofHom f) hT).trans_eq hM) bot_le

lemma zero_of_injective_torsion {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hT : powerTorsion I (ModuleCat.of R N)) (hN : ell.value (ModuleCat.of R N)=0) :
    ell.value (ModuleCat.of R M)=0 := by
  let : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
  exact le_antisymm ((ell.le_of_mono (ModuleCat.ofHom f) hT).trans_eq hN) bot_le

 

lemma iSup_zero_torsion (hds : ell.DirectSumZero) {ι M : Type u}
    [AddCommGroup M] [Module R M] (U : ι → Submodule R M)
    (hT : powerTorsion I (ModuleCat.of R M))
    (hU : ∀ i, ell.value (ModuleCat.of R (U i))=0) :
    ell.value (ModuleCat.of R (⨆ i,U i : Submodule R M))=0 := by
  classical
  obtain ⟨a,ha⟩ := hT
  have hUa : ∀ i, I^a ≤ Module.annihilator R (U i) := fun i =>
    ha.trans ((U i).subtype.annihilator_le_of_injective (U i).injective_subtype)
  have hsum : powerTorsion I (ModuleCat.of R (⨁ i,U i)) := by
    refine ⟨a,?_⟩
    change I^a ≤ Module.annihilator R (Π₀ i, U i)
    rw [Module.annihilator_dfinsupp]
    exact le_iInf hUa
  have hh := ell.zero_of_surjective_torsion (DirectSum.coeLinearMap U).rangeRestrict
    (DirectSum.coeLinearMap U).surjective_rangeRestrict hsum (hds (fun i => U i) a hUa hU)
  rwa [DirectSum.range_coeLinearMap] at hh

lemma zero_of_ranges_torsion (hds : ell.DirectSumZero) {ι M : Type u}
    [AddCommGroup M] [Module R M] {N : ι → Type u}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i,N i →ₗ[R] M)
    (hT : powerTorsion I (ModuleCat.of R M))
    (hNT : ∀ i,powerTorsion I (ModuleCat.of R (N i)))
    (hN : ∀ i,ell.value (ModuleCat.of R (N i))=0)
    (hspan : (⨆ i,(f i).range)=⊤) : ell.value (ModuleCat.of R M)=0 := by
  have hh := ell.iSup_zero_torsion hds (fun i => (f i).range) hT
    (fun i => ell.zero_of_surjective_torsion (f i).rangeRestrict
      (f i).surjective_rangeRestrict (hNT i) (hN i))
  rw [hspan,ell.value_linearEquiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M) hT] at hh
  exact hh

variable {A M N : Type u} [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

lemma tensor_torsion_right (hT : powerTorsion I (ModuleCat.of R N)) :
    powerTorsion I (ModuleCat.of R (M ⊗[A] N)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
      rw [←TensorProduct.tmul_smul,Module.mem_annihilator.mp (ha hr) n,TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add,hx,hy,add_zero]

lemma tensor_zero_right_torsion (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R N)) (hN : ell.value (ModuleCat.of R N)=0) :
    ell.value (ModuleCat.of R (M ⊗[A] N))=0 := by
  let f (m : M) : N →ₗ[R] M ⊗[A] N := (TensorProduct.mk A M N m).restrictScalars R
  apply ell.zero_of_ranges_torsion hds f (tensor_torsion_right hT) (fun _ => hT) (fun _ => hN)
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact (le_iSup (fun m => (f m).range) m) ⟨n,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

 

omit [Module R N] [IsScalarTower R A N] in
lemma tensor_map_kernel_zero_torsion (hds : ell.DirectSumZero)
    {V : Type u} [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hTk : powerTorsion I (ModuleCat.of R f.ker))
    (hker : ell.value (ModuleCat.of R f.ker)=0) :
    ell.value (ModuleCat.of R (f.lTensor V).ker)=0 := by
  let k := f.ker.subtype.lTensor V
  have he := _root_.lTensor_exact V f.exact_subtype_ker_map hf
  let q : V ⊗[A] f.ker →ₗ[R] (f.lTensor V).ker :=
    (k.restrictScalars R).codRestrict ((f.lTensor V).ker.restrictScalars R) (fun x => by
      change (f.lTensor V) (k x)=0
      exact he.apply_apply_eq_zero x)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v,hv⟩ := he x.val |>.mp x.property
    exact ⟨v,Subtype.ext hv⟩
  exact ell.zero_of_surjective_torsion q hq (tensor_torsion_right hTk)
    (ell.tensor_zero_right_torsion hds hTk hker)

end TorsionLength
end Lech

end

end OAI
