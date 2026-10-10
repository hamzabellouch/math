import Mathlib
import OAI.RingTheory.Multiplicity.CechCartierRange
import OAI.RingTheory.Multiplicity.IdealFilteredRows
import OAI.RingTheory.Multiplicity.ReesRootNilpotence

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ) (hgen : Ideal.span (Set.range z)=I)
  (p : ℤ) [Module.Flat R (F.X p)]

 
def enlargedRowNatIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℕ)).obj
      (cech I z hz (raise m (IdealFiltered.order h s p))) ≅
    ((IdealFiltered.rowFunctor I F h s hd p).mapHomologicalComplex (.up ℕ)).obj
      (cech I z hz m) :=
  IdealFiltered.rowIso I F h s hd _ _ p
    (cechInclusionIter I z hz m (IdealFiltered.order h s p))
    (cechInclusionIter_range I z hz m hgen (IdealFiltered.order h s p))
    (cechInclusionIter_injective I z hz m (IdealFiltered.order h s p))

 

def enlargedRowIso :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (cechZ I z hz (raise m (IdealFiltered.order h s p))) ≅
      (enlargedAt I z hz F h s hd m).X p :=
  ComplexExtension.mapExtendIso ((curriedTensor (ModuleCat.{u} R)).obj (F.X p))
      (cech I z hz (raise m (IdealFiltered.order h s p))) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (enlargedRowNatIso I z hz F h s hd m hgen p) ≪≫
    (ComplexExtension.mapExtendIso (IdealFiltered.rowFunctor I F h s hd p)
      (cech I z hz m)).symm
end Lech.ReesRoot

end

end OAI
