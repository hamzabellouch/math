import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredRows
import OAI.RingTheory.Multiplicity.IdealQuotientFunctor

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {M N : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (J K : Ideal R) (f : M →ₗ[R] N)

 
def restrictIdeal : ↥(K • (⊤ : Submodule R M)) →ₗ[R] ↥(K • (⊤ : Submodule R N)) :=
  (f.comp (K • (⊤ : Submodule R M)).subtype).codRestrict _
    (fun x => Submodule.smul_top_le_comap_smul_top K f x.property)

lemma restrictIdeal_val (x : ↥(K • (⊤ : Submodule R M))) :
    (restrictIdeal K f x).val=f x.val := rfl

lemma restrictIdeal_range (hf : f.range=J • (⊤ : Submodule R N)) :
    (restrictIdeal K f).range=J • (⊤ : Submodule R ↥(K • (⊤ : Submodule R N))) := by
  apply Submodule.map_injective_of_injective (K • (⊤ : Submodule R N)).subtype_injective
  rw [←LinearMap.range_comp,Submodule.map_smul'',Submodule.map_top,Submodule.range_subtype]
  change (f.comp (K • (⊤ : Submodule R M)).subtype).range = J • (K • (⊤ : Submodule R N))
  rw [LinearMap.range_comp,Submodule.range_subtype,Submodule.map_smul'',Submodule.map_top,hf,
    ←Submodule.mul_smul,←Submodule.mul_smul,mul_comm]

lemma restrictIdeal_injective (hf : Function.Injective f) :
    Function.Injective (restrictIdeal K f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)
end Lech.TensorIdeal

namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) {M N : ModuleCat.{u} R} (f : M ⟶ N)

lemma rowMap_eq :
    ((rowFunctor I F h s hd p).map f).hom =
      TensorIdeal.restrictIdeal (I^(order h s p)) (f.hom.lTensor (F.X p)) := rfl

lemma rowMap_range (hf : f.hom.range=I • (⊤ : Submodule R N)) :
    ((rowFunctor I F h s hd p).map f).hom.range =
      I • (⊤ : Submodule R ((rowFunctor I F h s hd p).obj N)) := by
  rw [rowMap_eq]
  apply TensorIdeal.restrictIdeal_range
  simpa only [pow_one] using TensorIdeal.range_lTensor I f.hom 1
    (by simpa only [pow_one] using hf) (F.X p)

lemma rowMap_injective [Module.Flat R (F.X p)] (hf : Function.Injective f.hom) :
    Function.Injective ((rowFunctor I F h s hd p).map f).hom := by
  rw [rowMap_eq]
  exact TensorIdeal.restrictIdeal_injective _ _
    (Module.Flat.lTensor_preserves_injective_linearMap f.hom hf)

end Lech.IdealFiltered

end

end OAI
