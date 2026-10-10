import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredComplex
import OAI.RingTheory.Multiplicity.TensorIdealRange

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

 
def rowFunctor (p : ℤ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  functor I F h s hd ⋙ HomologicalComplex.eval _ _ p

instance rowFunctor_additive (p : ℤ) : (rowFunctor I F h s hd p).Additive := by
  unfold rowFunctor
  infer_instance

variable {ι : Type*} {c : ComplexShape ι} (K L : HomologicalComplex (ModuleCat.{u} R) c)
  (p : ℤ) [Module.Flat R (F.X p)] (f : K ⟶ L)
  (hr : ∀ q,(f.f q).hom.range=I^(order h s p) • (⊤ : Submodule R (L.X q)))
  (hi : ∀ q,Function.Injective (f.f q).hom)

def rowTermEquiv (q : ι) :
    ((F.X p) ⊗[R] (K.X q)) ≃ₗ[R] (rowFunctor I F h s hd p).obj (L.X q) :=
  TensorIdeal.equiv I (f.f q).hom (order h s p) (hr q) (F.X p) (hi q)

lemma rowTermEquiv_val (q : ι) (x : (F.X p) ⊗[R] (K.X q)) :
    (rowTermEquiv I F h s hd K L p f hr hi q x).val =
      (f.f q).hom.lTensor (F.X p) x := rfl

lemma rowTermEquiv_natural (q r : ι) (x : (F.X p) ⊗[R] (K.X q)) :
    ((rowFunctor I F h s hd p).map (L.d q r)).hom
      (rowTermEquiv I F h s hd K L p f hr hi q x) =
    rowTermEquiv I F h s hd K L p f hr hi r
      ((K.d q r).hom.lTensor (F.X p) x) := by
  apply Subtype.ext
  change (L.d q r).hom.lTensor (F.X p) ((f.f q).hom.lTensor (F.X p) x) =
    (f.f r).hom.lTensor (F.X p) ((K.d q r).hom.lTensor (F.X p) x)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b =>
      simp only [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg (fun g : K.X q ⟶ L.X r => g.hom b) (f.comm q r)

 
def rowIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex c).obj K ≅
      ((rowFunctor I F h s hd p).mapHomologicalComplex c).obj L :=
  Hom.isoOfComponents (fun q => (rowTermEquiv I F h s hd K L p f hr hi q).toModuleIso) (by
    intro q r hqr
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact rowTermEquiv_natural I F h s hd K L p f hr hi q r x)

end Lech.IdealFiltered

end

end OAI
