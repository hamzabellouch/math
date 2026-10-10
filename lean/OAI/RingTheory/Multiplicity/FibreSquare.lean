import Mathlib
import OAI.RingTheory.Multiplicity.TensorCoefficientFibre
import OAI.RingTheory.Multiplicity.TorsionChartKernel
import OAI.RingTheory.Multiplicity.TorsionTensorLeft

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u
section Quotient
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

def idealQuotientMap (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
  Submodule.mapQ _ _ f (by
    rw [←Submodule.map_le_iff_le_comap,Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

lemma idealQuotientMap_mk (f : M →ₗ[R] N) (x : M) :
    idealQuotientMap I f (Submodule.Quotient.mk x)=Submodule.Quotient.mk (f x) := rfl

lemma quotientTensorEquiv_mk {A P Q : Type u} [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    (f : P →ₗ[A] Q) (hf : Function.Surjective f)
    (hker : (f.restrictScalars R).ker = I • (⊤ : Submodule R P))
    (V : Type u) [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (p : P) (v : V) :
    quotientTensorEquiv I f hf hker V (Submodule.Quotient.mk (p ⊗ₜ[A] v))=f p ⊗ₜ[A] v := by
  change (((f.rTensor V).restrictScalars R).quotKerEquivOfSurjective
    (LinearMap.rTensor_surjective V hf))
      ((Submodule.quotEquivOfEq _ _ (kernel_rTensor I f hf hker V).symm)
        (Submodule.Quotient.mk (p ⊗ₜ[A] v))) = _
  rw [Submodule.quotEquivOfEq_mk]
  rfl
def kernelSquareEquiv {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    (e : M ≃ₗ[R] P) (e' : N ≃ₗ[R] Q) (h : ∀ x,e' (f x)=g (e x)) :
    f.ker ≃ₗ[R] g.ker :=
  e.ofSubmodules _ _ (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    change f (e.symm x)=0 ↔ g x=0
    calc
      _ ↔ e' (f (e.symm x))=0 := (map_eq_zero_iff _ e'.injective).symm
      _ ↔ g x=0 := by rw [h,e.apply_symm_apply])

end Quotient

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

abbrev unitMap : V →ₗ[R] B ⊗[A] V := (TensorProduct.mk A B V 1).restrictScalars R

def fibreMap : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R]
    ((B ⊗[A] V) ⧸ (I • (⊤ : Submodule R (B ⊗[A] V)))) :=
  idealQuotientMap I (unitMap (B:=B) V)

include hsq in
lemma fibre_square (x : V ⧸ (I • (⊤ : Submodule R V))) :
    quotientTensorEquiv I b hb hkb V (fibreMap I (A:=A) (B:=B) V x) =
      g.rTensor V (quotientUnitTensorEquiv I a ha hka V x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
    rw [fibreMap,idealQuotientMap_mk,quotientUnitTensorEquiv_mk]
    change quotientTensorEquiv I b hb hkb V (Submodule.Quotient.mk (1 ⊗ₜ[A] v)) = _
    rw [quotientTensorEquiv_mk,hsq]
    rfl

include ha hb hka hkb hsq in
lemma fibreMap_surjective (hg : Function.Surjective g) :
    Function.Surjective (fibreMap I (A:=A) (B:=B) V) := by
  intro x
  obtain ⟨y,hy⟩ := LinearMap.rTensor_surjective V hg (quotientTensorEquiv I b hb hkb V x)
  refine ⟨(quotientUnitTensorEquiv I a ha hka V).symm y,?_⟩
  apply (quotientTensorEquiv I b hb hkb V).injective
  rw [fibre_square I a b g ha hb hka hkb hsq V,LinearEquiv.apply_symm_apply,hy]

def fibreKernelEquiv : (fibreMap I (A:=A) (B:=B) V).ker ≃ₗ[R]
    ((g.rTensor V).restrictScalars R).ker :=
  kernelSquareEquiv (fibreMap I (A:=A) (B:=B) V) ((g.rTensor V).restrictScalars R)
    (quotientUnitTensorEquiv I a ha hka V) (quotientTensorEquiv I b hb hkb V)
      (fibre_square I a b g ha hb hka hkb hsq V)

include ha hb hka hkb hsq in
lemma fibreMap_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hg : Function.Surjective g) (hTc : powerTorsion I (ModuleCat.of R C))
    (hkg : ell.value (ModuleCat.of R g.ker)=0) :
    ell.value (ModuleCat.of R (fibreMap I (A:=A) (B:=B) V).ker)=0 := by
  have ht := TorsionLength.tensor_torsion_left (A:=A) (N:=V) hTc
  have htk := powerTorsion_submodule I ((g.rTensor V).ker.restrictScalars R) ht
  have he := ell.value_linearEquiv (fibreKernelEquiv I a b g ha hb hka hkb hsq V) htk
  exact he.trans (ell.rTensor_map_kernel_zero_torsion hds g hg
    (powerTorsion_submodule I (g.ker.restrictScalars R) hTc) hkg)

end Square
end Lech.TensorIdeal

end

end OAI
