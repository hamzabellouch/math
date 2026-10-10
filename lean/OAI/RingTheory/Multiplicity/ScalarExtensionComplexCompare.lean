import Mathlib
import OAI.RingTheory.Multiplicity.ComplexTensorComparison

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def tensorScalarExtensionObjIso (M : ModuleCat.{u} R) :
    ModuleCat.of R (M ⊗[R] S) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let c : S ≃ₗ[R] N :=
    { __ := (AddEquiv.refl S)
      map_smul' r x := Algebra.smul_def r x }
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  let e : N ⊗[R] M ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
    { __ := (AddEquiv.refl (N ⊗[R] M))
      map_smul' r x := by
        change N ⊗[R] M at x
        change r • x = algebraMap R S r • x
        exact (IsScalarTower.algebraMap_smul S r x).symm }
  exact ((TensorProduct.comm R M S).trans
    ((TensorProduct.congr c (LinearEquiv.refl R M)).trans e)).toModuleIso

def tensorScalarExtensionIso (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).obj (ModuleCat.of R S) ≅
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F) :=
  Hom.isoOfComponents (fun i => tensorScalarExtensionObjIso (F.X i)) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
lemma restriction_homology_length
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    Module.length R
      ((((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) =
      Module.length S (F.homology i) := by
  rw [(restrictionHomologyIso (algebraMap R S) F i).toLinearEquiv.length_eq]
  let M := (ModuleCat.restrictScalars (algebraMap R S)).obj (F.homology i)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  exact RootTower.length_eq_of_residue_surjective hres M

lemma restriction_scalar_quotient_homology_length
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (g : R) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => (algebraMap R S g) • x)) :
    Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i) =
      Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj F).homology i) := by
  let E := (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)
  let e := scalarQuotientTransport E F (algebraMap R S g) g (by
    rw [restrictScalars_complex_smul,CategoryTheory.Functor.map_id]) hg hg
  rw [← (homologyMapIso e i).toLinearEquiv.length_eq]
  exact restriction_homology_length hres _ i

 
theorem exists_scalar_extension_homology_bound
    [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) :
    ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
      (∀ j,Function.Injective (fun x : (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).X j =>
        (algebraMap R S g) • x)) →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≠ ⊤ →
      Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) ≤
        r • Module.length R (F.homology i) +
          Module.length S (((complexQuotient (Ideal.span {algebraMap R S g}) (.up ℤ)).obj
            (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj F)).homology i) := by
  obtain ⟨r,g,hg,hbound⟩ := exists_tensor_homology_bound (ModuleCat.of R S)
  refine ⟨r,g,hg,fun F i hgi hfin => ?_⟩
  let G := ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F
  let H := ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj G
  let e := tensorScalarExtensionIso F (S:=S)
  have hlen := (homologyMapIso e i).toLinearEquiv.length_eq.trans (restriction_homology_length hres G i)
  have hT (j : ℤ) : Function.Injective (fun x : ((tensorModuleFunctor F).obj (ModuleCat.of R S)).X j => g • x) := by
    let a := ((eval (ModuleCat R) (.up ℤ) j).mapIso e).toLinearEquiv
    intro x y hxy
    apply a.injective
    apply hgi j
    exact (a.map_smul g x).symm.trans ((congrArg a hxy).trans (a.map_smul g y))
  have hb := hbound F i hT (by rw [hlen]; exact hfin)
  rw [hlen] at hb
  have heq := (homologyMapIso ((complexQuotient (Ideal.span {g}) (.up ℤ)).mapIso e) i).toLinearEquiv.length_eq
  rw [heq,restriction_scalar_quotient_homology_length hres G g i hgi] at hb
  exact hb
end Lech

end

end OAI
