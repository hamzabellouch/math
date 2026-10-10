import Mathlib
import OAI.RingTheory.Multiplicity.ScalarExtensionFiniteHomology

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R]

def tensorModuleFunctor (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := (TensorTotal.termTensor M).obj F
  map f := TensorTotal.termTensorMap F _ f
  map_id M := by
    ext i : 1
    exact whiskerLeft_id (F.X i) M
  map_comp f g := TensorTotal.termTensorMap_comp F f g

instance tensorModuleFunctor_additive (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).Additive where
  map_add := by
    intros M N f g
    ext i : 1
    exact Functor.map_add ((curriedTensor (ModuleCat R)).obj (F.X i))

lemma tensorModuleFunctor_smul (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (a : R) (f : M ⟶ N) :
    (tensorModuleFunctor F).map (a • f) = a • (tensorModuleFunctor F).map f := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change x ⊗ₜ[R] (a • f y) = a • (x ⊗ₜ[R] f y)
  exact TensorProduct.tmul_smul _ _ _

def tensorModuleUnitIso (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorModuleFunctor F).obj (ModuleCat.of R R) ≅ F :=
  Hom.isoOfComponents (fun i => (TensorProduct.rid R (F.X i)).toModuleIso) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x
    change F.d i j ((1:R) • x) = (1:R) • F.d i j x
    exact map_smul _ _ _)

lemma tensorModule_homology_length_free [Nontrivial R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] (i : ℤ) :
    Module.length R (((tensorModuleFunctor F).obj M).homology i) =
      Module.finrank R M • Module.length R (F.homology i) := by
  change Module.length R (((tensorModuleFunctor F) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) i).obj M) = _
  rw [additive_length_finite_free
    ((tensorModuleFunctor F) ⋙ homologyFunctor (ModuleCat R) (.up ℤ) i) M]
  congr 1
  exact ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso (tensorModuleUnitIso F)).toLinearEquiv.length_eq

 

theorem exists_tensor_homology_bound [IsDomain R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (r : ℕ) (g : R), g ≠ 0 ∧ ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
      (∀ j,Function.Injective (fun x : ((tensorModuleFunctor F).obj M).X j => g • x)) →
      Module.length R (((tensorModuleFunctor F).obj M).homology i) ≠ ⊤ →
      Module.length R (((tensorModuleFunctor F).obj M).homology i) ≤
        r • Module.length R (F.homology i) +
          Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
            ((tensorModuleFunctor F).obj M)).homology i) := by
  obtain ⟨r,g,hg,u,v,huv,hvu⟩ := finite_free_factorization R M
  refine ⟨r,g,hg,fun F i hgi hfin => ?_⟩
  let U : ModuleCat.of R (Fin r → R) ⟶ M := ModuleCat.ofHom u
  let V : M ⟶ ModuleCat.of R (Fin r → R) := ModuleCat.ofHom v
  have hVU : V ≫ U = g • 𝟙 M := ModuleCat.hom_ext huv
  have he := congrArg (tensorModuleFunctor F).map hVU
  rw [CategoryTheory.Functor.map_comp,tensorModuleFunctor_smul,
    CategoryTheory.Functor.map_id] at he
  have hb := homology_length_le_of_scalar_retract
    ((tensorModuleFunctor F).map V) ((tensorModuleFunctor F).map U) g he i hgi hfin
  rw [tensorModule_homology_length_free F (ModuleCat.of R (Fin r → R)) i] at hb
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using hb
end Lech

end

end OAI
