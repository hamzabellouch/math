import Mathlib
import OAI.RingTheory.Multiplicity.ComplexConductor
import OAI.RingTheory.Multiplicity.FrobeniusComplexStage

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def scalarQuotientCokernelIso (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) :
    ((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F) ≅ cokernel (g • 𝟙 F) :=
  (scalarQuotientShortExact g F hg).gIsCokernel.coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (g • 𝟙 F) 0))

def scalarQuotientTransport
    (E : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ)
    [E.PreservesZeroMorphisms] [PreservesFiniteColimits E]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (g : R) (a : S)
    (hmap : E.map (g • 𝟙 F) = a • 𝟙 (E.obj F))
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (ha : ∀ j,Function.Injective (fun x : (E.obj F).X j => a • x)) :
    E.obj ((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F) ≅
      ((complexQuotient (Ideal.span {a}) (.up ℤ)).obj (E.obj F)) :=
  E.mapIso (scalarQuotientCokernelIso g F hg) ≪≫
    PreservesCokernel.iso E _ ≪≫ cokernelIsoOfEq hmap ≪≫
    (scalarQuotientCokernelIso a (E.obj F) ha).symm

lemma free_scalar_injective [IsDomain R] (M : ModuleCat.{u} R) [Module.Free R M]
    (g : R) (hg : g ≠ 0) : Function.Injective (fun x : M => g • x) :=
  smul_right_injective M hg
end Lech

end

end OAI
