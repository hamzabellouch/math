import Mathlib
import OAI.RingTheory.Multiplicity.CechNormalization
import OAI.RingTheory.Multiplicity.TensorTotalHomologyProperty

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

def extendEquivalence {K L : CochainComplex (ModuleCat.{u} R) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingUpNat) (L.extend ComplexShape.embeddingUpNat) where
  hom := extendMap e.hom ComplexShape.embeddingUpNat
  inv := extendMap e.inv ComplexShape.embeddingUpNat
  homotopyHomInvId := by
    simpa only [extendMap_comp,extendMap_id] using e.homotopyHomInvId.extend ComplexShape.embeddingUpNat
  homotopyInvHomId := by
    simpa only [extendMap_comp,extendMap_id] using e.homotopyInvHomId.extend ComplexShape.embeddingUpNat

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
def tensorHomotopy {K L : CochainComplex (ModuleCat.{u} R) ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy ((TensorTotal.Right.functor F).map f) ((TensorTotal.Right.functor F).map g) :=
  mapBifunctorMapHomotopy₂ (𝟙 F) h (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

def tensorEquivalence {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((TensorTotal.Right.functor F).obj K) ((TensorTotal.Right.functor F).obj L) where
  hom := (TensorTotal.Right.functor F).map e.hom
  inv := (TensorTotal.Right.functor F).map e.inv
  homotopyHomInvId := by
    have h := tensorHomotopy F e.homotopyHomInvId
    erw [(TensorTotal.Right.functor F).map_comp e.hom e.inv, (TensorTotal.Right.functor F).map_id K] at h
    exact h
  homotopyInvHomId := by
    have h := tensorHomotopy F e.homotopyInvHomId
    erw [(TensorTotal.Right.functor F).map_comp e.inv e.hom, (TensorTotal.Right.functor F).map_id L] at h
    exact h
end Lech.CechNormalization

end

end OAI
