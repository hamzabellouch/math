import Mathlib
import OAI.RingTheory.Multiplicity.FiniteComplexTopInclusion

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (P M : ModuleCat.{u} R) (b : ℕ)
  (B : Module.Basis (Fin b) R P)

def tensorBasisEquiv : (P ⊗[R] M) ≃ₗ[R] (Fin b → M) :=
  TensorProduct.congr B.equivFun (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.piLeft R M (fun _ : Fin b => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R M)

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
  [Module.Flat R P]

def tensorHomologyIso (q : ι) :
    ((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q ≅
      ModuleCat.of R (P ⊗[R] K.homology q) :=
  (K.sc q).mapHomologyIso ((curriedTensor (ModuleCat.{u} R)).obj P)

def tensorHomologyBasisIso (q : ι) :
    ((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q ≅
      ModuleCat.of R (Fin b → K.homology q) :=
  tensorHomologyIso P K q ≪≫ (tensorBasisEquiv P (K.homology q) b B).toModuleIso

variable (I : Ideal R) (ell : TorsionLength I)
include B in
lemma tensorHomology_torsion (q : ι) (ht : powerTorsion I (K.homology q)) :
    powerTorsion I
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q) :=
  (powerTorsion I).prop_of_iso (tensorHomologyBasisIso P b B K q).symm
    (powerTorsion_fin b ht)

include B in
lemma tensorHomology_length (q : ι) (ht : powerTorsion I (K.homology q)) :
    ell.value
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q) =
        b • ell.value (K.homology q) :=
  (ell.eq_of_iso (tensorHomologyBasisIso P b B K q)
    (tensorHomology_torsion P b B K I q ht) (powerTorsion_fin b ht)).trans
      (ell.value_fin ht b)

include B in
lemma tensorHomology_length_finite (q : ι) (ht : powerTorsion I (K.homology q))
    (hf : ell.value (K.homology q)≠⊤) :
    ell.value
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q)≠⊤ := by
  rw [tensorHomology_length P b B K I ell q ht,nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) hf
end Lech.TensorIdeal

end

end OAI
