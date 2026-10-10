import Mathlib
import OAI.RingTheory.Multiplicity.ScalarExtensionFiniteHomology

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def zeroHomologyCokernelIso (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hzero : F.d 0 1 = 0) : F.homology 0 ≅ cokernel (F.d (-1) 0) :=
  F.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    (F.sc' (-1) 0 1).asIsoHomologyι hzero ≪≫ (F.sc' (-1) 0 1).opcyclesIsoCokernel

def scalarExtensionZeroHomologyIso (φ : R →+* S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hzero : F.d 0 1 = 0) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F).homology 0 ≅
      (ModuleCat.extendScalars φ).obj (F.homology 0) := by
  let E := ModuleCat.extendScalars φ
  let G := (E.mapHomologicalComplex (.up ℤ)).obj F
  have hz : G.d 0 1 = 0 := by
    change E.map (F.d 0 1) = 0
    rw [hzero,CategoryTheory.Functor.map_zero]
  exact zeroHomologyCokernelIso G hz ≪≫ (PreservesCokernel.iso E (F.d (-1) 0)).symm ≪≫
    E.mapIso (zeroHomologyCokernelIso F hzero).symm

variable [IsNoetherianRing R] [IsLocalRing R]
omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsFiniteHomologyComplex.d_zero_one_eq_zero
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsFiniteHomologyComplex R F) :
    F.d 0 1 = 0 :=
  (hF.bounded 1 (Or.inr (by omega))).eq_of_tgt _ _
end Lech

end

end OAI
