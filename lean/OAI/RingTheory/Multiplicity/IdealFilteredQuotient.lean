import Mathlib
import OAI.RingTheory.Multiplicity.ModuleComplexQuotient
import OAI.RingTheory.Multiplicity.TensorQuotientCommutation

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

abbrev quotientComplex (Q : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ModuleComplexQuotient.complex (tensorComplex F Q) (term I F h s Q) (term_d I F h s hd Q)

def quotientMap {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    quotientComplex I F h s hd Q ⟶ quotientComplex I F h s hd Q' :=
  ModuleComplexQuotient.map (tensorMap F f)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F f).f p).hom)

lemma quotientMap_id (Q : ModuleCat.{u} R) :
    quotientMap I F h s hd (𝟙 Q)=𝟙 (quotientComplex I F h s hd Q) := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change Submodule.Quotient.mk ((F.X p ◁ 𝟙 Q).hom x)=Submodule.Quotient.mk x
      rw [whiskerLeft_id]
      rfl

lemma quotientMap_comp {Q Q' Q'' : ModuleCat.{u} R} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    quotientMap I F h s hd (f ≫ g)=quotientMap I F h s hd f ≫ quotientMap I F h s hd g := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change Submodule.Quotient.mk ((F.X p ◁ (f ≫ g)).hom x)=
        Submodule.Quotient.mk ((F.X p ◁ g).hom ((F.X p ◁ f).hom x))
      rw [whiskerLeft_comp]
      rfl

 
def quotientFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := quotientComplex I F h s hd
  map := quotientMap I F h s hd
  map_id := quotientMap_id I F h s hd
  map_comp := quotientMap_comp I F h s hd

instance quotientFunctor_additive : (quotientFunctor I F h s hd).Additive where
  map_add := by
    intro Q Q' f g
    apply Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change (term I F h s Q' p).mkQ ((F.X p ◁ (f+g)).hom x)=
          (term I F h s Q' p).mkQ ((F.X p ◁ f).hom x)+(term I F h s Q' p).mkQ ((F.X p ◁ g).hom x)
        rw [show F.X p ◁ (f+g)=F.X p ◁ f+F.X p ◁ g from
          ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).map_add]
        rfl

 
def quotientRowIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (((TensorIdeal.quotientFunctor (I^(order h s p))).mapHomologicalComplex (.up ℤ)).obj K) ≅
      (HomologicalComplex₂.flip (((quotientFunctor I F h s hd).mapHomologicalComplex (.up ℤ)).obj K)).X p :=
  (NatIso.mapHomologicalComplex (TensorIdeal.tensorReductionIso (I^(order h s p)) (F.X p)) (.up ℤ)).app K
end Lech.IdealFiltered

end

end OAI
