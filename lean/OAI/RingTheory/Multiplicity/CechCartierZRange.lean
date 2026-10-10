import Mathlib
import OAI.RingTheory.Multiplicity.CechCartierRange
import OAI.RingTheory.Multiplicity.ReesRootNilpotence

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R)
  {M N M' N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M' ⟶ N')
  (e : M' ≅ M) (e' : N' ≅ N)
lemma range_of_square (hsq : g ≫ e'.hom=e.hom ≫ f)
    (hf : f.hom.range=J • (⊤ : Submodule R N)) :
    g.hom.range=J • (⊤ : Submodule R N') := by
  apply Submodule.map_injective_of_injective ((ModuleCat.mono_iff_injective e'.hom).mp inferInstance)
  rw [←LinearMap.range_comp]
  have he : e'.hom.hom.comp g.hom=f.hom.comp e.hom.hom := congrArg ModuleCat.Hom.hom hsq
  rw [he,LinearMap.range_comp,(LinearMap.range_eq_top.mpr
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)),Submodule.map_top,hf,
    Submodule.map_smul'',Submodule.map_top,(LinearMap.range_eq_top.mpr
      ((ModuleCat.epi_iff_surjective e'.hom).mp inferInstance))]

lemma injective_of_square (hsq : g ≫ e'.hom=e.hom ≫ f)
    (hf : Function.Injective f.hom) : Function.Injective g.hom := by
  intro x y hxy
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply hf
  have hx := congrArg (fun a : M' ⟶ N => a.hom x) hsq
  have hy := congrArg (fun a : M' ⟶ N => a.hom y) hsq
  change e'.hom.hom (g.hom x)=f.hom (e.hom.hom x) at hx
  change e'.hom.hom (g.hom y)=f.hom (e.hom.hom y) at hy
  rw [←hx,←hy,hxy]
end Lech.TensorIdeal

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

lemma cechInclusionZ_square (a q : ℕ) :
    (cechInclusionZ I z hz m a).f (q:ℤ) ≫
        ((cech I z hz m).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).hom =
      ((cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat (i:=q) rfl).hom ≫
        (cechInclusionIter I z hz m a).f q := by
  let e := (cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  let e' := (cech I z hz m).extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  have he := extendMap_f (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl)
  exact (congrArg (fun f => f ≫ e'.hom) he).trans (by
    change (e.hom ≫ (cechInclusionIter I z hz m a).f q ≫ e'.inv) ≫ e'.hom =
      e.hom ≫ (cechInclusionIter I z hz m a).f q
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

lemma cechInclusionZ_range (hgen : Ideal.span (Set.range z)=I) (a : ℕ) (q : ℤ) :
    ((cechInclusionZ I z hz m a).f q).hom.range =
      I^a • (⊤ : Submodule R ((cechZ I z hz m).X q)) := by
  cases q with
  | ofNat q =>
      exact TensorIdeal.range_of_square (I^a) _ _ _ _ (cechInclusionZ_square I z hz m a q)
        (cechInclusionIter_range I z hz m hgen a q)
  | negSucc q =>
      have hzq := cechZ_negative I z hz m (Int.negSucc q) (by omega)
      have : Subsingleton ((cechZ I z hz m).X (Int.negSucc q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzq
      exact Subsingleton.elim _ _

lemma cechInclusionZ_injective (a : ℕ) (q : ℤ) :
    Function.Injective ((cechInclusionZ I z hz m a).f q).hom := by
  cases q with
  | ofNat q =>
      exact TensorIdeal.injective_of_square _ _ _ _ (cechInclusionZ_square I z hz m a q)
        (cechInclusionIter_injective I z hz m a q)
  | negSucc q =>
      have hzq := cechZ_negative I z hz (raise m a) (Int.negSucc q) (by omega)
      have : Subsingleton ((cechZ I z hz (raise m a)).X (Int.negSucc q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzq
      exact Function.injective_of_subsingleton _
end Lech.ReesRoot

end

end OAI
