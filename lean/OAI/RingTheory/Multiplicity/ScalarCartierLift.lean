import Mathlib
import OAI.RingTheory.Multiplicity.SignedCechBicRow

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
  (f : M ⟶ N) (hf : Function.Injective f.hom) (J : Ideal R)
  (hr : f.hom.range=J • (⊤ : Submodule R N)) (a : R) (ha : a∈J)

def scalarLift : N ⟶ M := ModuleCat.ofHom
  ((LinearEquiv.ofInjective f.hom hf).symm.toLinearMap.comp
    ((a • (LinearMap.id : N →ₗ[R] N)).codRestrict f.hom.range (fun x => by
      rw [hr]
      exact Submodule.smul_mem_smul ha Submodule.mem_top)))

include hf hr ha in
lemma scalarLift_comp : scalarLift f hf J hr a ha ≫ f=a • 𝟙 N := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f.hom ((LinearEquiv.ofInjective f.hom hf).symm _) = a • x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective f.hom hf).apply_symm_apply _)
end Lech.TensorIdeal

namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {K L : Bic (R:=R)}
  (f : K ⟶ L) (hf : ∀ p q,Function.Injective ((f.f p).f q).hom) (J : Ideal R)
  (hr : ∀ p q,((f.f p).f q).hom.range=J • (⊤ : Submodule R ((L.X p).X q)))
  (a : R) (ha : a∈J)
def scalarRowLift (p : ℤ) : L.X p ⟶ K.X p := by
  letI : ∀ q, Mono ((f.f p).f q) :=
    fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.lift (f.f p) (a • 𝟙 (L.X p))
    (fun q => TensorIdeal.scalarLift ((f.f p).f q) (hf p q) J (hr p q) a ha)
    (fun q => TensorIdeal.scalarLift_comp ((f.f p).f q) (hf p q) J (hr p q) a ha)

include hf hr ha in
lemma scalarRowLift_comp (p : ℤ) : scalarRowLift f hf J hr a ha p ≫ f.f p=a • 𝟙 (L.X p) := by
  let : ∀ q, Mono ((f.f p).f q) :=
    fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.lift_comp _ _ _ _

 

def scalarLift : L ⟶ K := by
  letI : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.lift f (a • 𝟙 L) (scalarRowLift f hf J hr a ha)
    (scalarRowLift_comp f hf J hr a ha)

include hf hr ha in
lemma scalarLift_comp : scalarLift f hf J hr a ha ≫ f=a • 𝟙 L := by
  let : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.lift_comp _ _ _ _

lemma total_map_smul (a : R) (f : K ⟶ L) :
    total.map (a • f) (.up ℤ)=a • total.map f (.up ℤ) := by
  apply Hom.ext
  funext i
  apply total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.smul_f_apply,ιTotal_map,CategoryTheory.Linear.comp_smul,
    CategoryTheory.Linear.smul_comp]

include hf hr in
 
lemma annihilator_of_nilpotence (i : ℤ) (hnil : homologyMap (total.map f (.up ℤ)) i=0) :
    J ≤ Module.annihilator R ((L.total (.up ℤ)).homology i) := by
  intro a ha
  rw [Module.mem_annihilator]
  have he := congrArg (fun g => homologyMap (total.map g (.up ℤ)) i)
    (scalarLift_comp f hf J hr a ha)
  rw [total.map_comp,homologyMap_comp,hnil,comp_zero,total_map_smul,total.map_id,
    Lech.homologyMap_smul,homologyMap_id] at he
  intro x
  exact (congrArg (fun g : (L.total (.up ℤ)).homology i ⟶ (L.total (.up ℤ)).homology i => g.hom x) he).symm
end Lech.TotalGhost

end

end OAI
