import Mathlib
import OAI.RingTheory.Multiplicity.CompleteQuotient
import OAI.RingTheory.Multiplicity.TensorEuler
import OAI.RingTheory.Multiplicity.ZeroHomologyScalarExtension

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance quotient_local (P : Ideal R) [P.IsPrime] : IsLocalRing (R ⧸ P) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
local instance quotient_localHom (P : Ideal R) [P.IsPrime] : IsLocalHom (Ideal.Quotient.mk P) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
lemma quotient_residue_surjective [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] :
    Function.Surjective (algebraMap (ResidueField R) (ResidueField (R ⧸ P))) := by
  intro x
  obtain ⟨a,rfl⟩ := residue_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨residue R b,rfl⟩

def quotientResidueEquiv (P : Ideal R) [P.IsPrime] :
    ResidueField R ≃+* ResidueField (R ⧸ P) :=
  RingEquiv.ofBijective (algebraMap _ _)
    ⟨RingHom.injective _,quotient_residue_surjective P⟩

lemma isAlgClosed_quotient_residue [IsAlgClosed (ResidueField R)] (P : Ideal R) [P.IsPrime] :
    IsAlgClosed (ResidueField (R ⧸ P)) :=
  IsAlgClosed.of_ringEquiv (ResidueField R) (ResidueField (R ⧸ P)) (quotientResidueEquiv P)

omit [IsNoetherianRing R] in
lemma quotient_tensor_subsingleton [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : Subsingleton (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).obj M))) :
    Subsingleton M := by
  let φ := Ideal.Quotient.mk P
  let := φ.toAlgebra
  have he := TensorProduct.quotTensorEquivQuotSMul M P
  let : Subsingleton ((R ⧸ P) ⊗[R] M) := h
  have hz : Subsingleton (M ⧸ P • (⊤ : Submodule R M)) :=
    he.toEquiv.surjective.subsingleton
  have htop := Submodule.Quotient.subsingleton_iff.mp hz
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot P (⊤ : Submodule R M)
    Module.Finite.fg_top htop.ge
    ((le_maximalIdeal (show P ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)).trans
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]))
  have hzero : ∀ x : M,x=0 := by
    intro x
    exact (Submodule.mem_bot R).mp (hbot ▸ (Submodule.mem_top : x ∈ (⊤:Submodule R M)))
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

lemma shortComplex_quotient (P : Ideal R) [P.IsPrime]
    (hd : dimension (R ⧸ P)=dimension R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    IsShortComplex (R ⧸ P)
      (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F) := by
  have hh := finiteHomology_extendScalars (Ideal.Quotient.mk P) hd
    (PrimeFiltration.primary_quotient (maximalIdeal R) P (Ideal.IsPrime.radical inferInstance))
    F hF.finiteHomology
  refine ⟨hh.term_free,hh.term_finite,hh.bounded,hh.homology_finite_length,?_⟩
  intro hz
  have e := scalarExtensionZeroHomologyIso (Ideal.Quotient.mk P) F
    hF.finiteHomology.d_zero_one_eq_zero
  have hz' := ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso e.symm)
  have : IsNoetherian R (F.homology 0) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hF.homology_finite_length 0)).1
  exact hF.homology_zero_nonzero (ModuleCat.isZero_iff_subsingleton.mpr
    (quotient_tensor_subsingleton P (F.homology 0) hz'))
end Lech

end

end OAI
