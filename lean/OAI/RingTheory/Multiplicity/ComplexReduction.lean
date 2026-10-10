import Mathlib
import OAI.RingTheory.Multiplicity.TensorQuotientCommutation

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {ι : Type*} (c : ComplexShape ι)

def complexQuotientNat : 𝟭 (HomologicalComplex (ModuleCat.{u} R) c) ⟶
    (quotientFunctor I).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) c).inv ≫
    (quotientNat I).mapHomologicalComplex c

lemma complexQuotientNat_f (K : HomologicalComplex (ModuleCat.{u} R) c) (q : ι) :
    ((complexQuotientNat I c).app K).f q=(quotientNat I).app (K.X q) := by
  change (𝟙 (K.X q)) ≫ (quotientNat I).app (K.X q)=_
  exact Category.id_comp _

variable {κ : Type*} (d : ComplexShape κ)
def bicomplexQuotientNat :
    𝟭 (HomologicalComplex (HomologicalComplex (ModuleCat.{u} R) c) d) ⟶
      ((quotientFunctor I).mapHomologicalComplex c).mapHomologicalComplex d :=
  (Functor.mapHomologicalComplexIdIso (HomologicalComplex (ModuleCat.{u} R) c) d).inv ≫
    (complexQuotientNat I c).mapHomologicalComplex d

lemma bicomplexQuotientNat_f (K : HomologicalComplex (HomologicalComplex (ModuleCat.{u} R) c) d)
    (p : κ) (q : ι) :
    (((bicomplexQuotientNat I c d).app K).f p).f q=(quotientNat I).app ((K.X p).X q) := by
  change ((𝟙 (K.X p)) ≫ (complexQuotientNat I c).app (K.X p)).f q=_
  rw [Category.id_comp,complexQuotientNat_f]
end Lech.TensorIdeal

end

end OAI
