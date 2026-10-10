import Mathlib
import OAI.RingTheory.Multiplicity.FiniteLengthPrimary
import OAI.RingTheory.Multiplicity.FiniteModuleTensor
import OAI.RingTheory.Multiplicity.TowerRestrictedLength

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u
lemma extendScalars_annihilator {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map φ ≤ Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change I.map φ ≤ Module.annihilator S (S ⊗[R] M)
  exact Lech.NormalizedLength.map_le_annihilator_baseChange I hI

lemma extendScalars_generators {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) {b : ℕ} (f : (Fin b → R) →ₗ[R] M)
    (hf : Function.Surjective f) :
    ∃ g : (Fin b → S) →ₗ[S] ((ModuleCat.extendScalars φ).obj M), Function.Surjective g := by
  let := φ.toAlgebra
  change ∃ g : (Fin b → S) →ₗ[S] (S ⊗[R] M), Function.Surjective g
  exact ⟨Lech.TensorGenerator.baseGenerators f S,
    Lech.TensorGenerator.baseGenerators_surjective f S hf⟩

lemma finiteLength_of_primary_annihilator {S N : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (I : Ideal S) (hI : I.radical = IsLocalRing.maximalIdeal S)
    (hIN : I ≤ Module.annihilator S N) : IsFiniteLength S N := by
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' S N
  apply Module.length_ne_top_iff.mp
  have hIfin := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at hIfin
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top b) hIfin)
    (length_le_quotient_generators I hIN f hf)

lemma finiteLength_extendScalars_of_primary {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M] (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) (hφ : (I.map φ).radical = IsLocalRing.maximalIdeal S) :
    IsFiniteLength S ((ModuleCat.extendScalars φ).obj M) := by
  have := finite_extendScalars φ M
  exact finiteLength_of_primary_annihilator _ hφ (extendScalars_annihilator φ M I hI)

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
variable (M : ModuleCat.{u} D)

lemma frobeniusModule_annihilator (I : Ideal D) (hI : I ≤ Module.annihilator D M) (n : ℕ) :
    I.map (iterateFrobenius D p n) ≤ Module.annihilator D (FrobeniusModule D p n M) :=
  extendScalars_annihilator (iterateFrobenius D p n) M I hI

lemma frobeniusModule_generators {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
    (hf : Function.Surjective f) (n : ℕ) :
    ∃ g : (Fin b → D) →ₗ[D] (FrobeniusModule D p n M), Function.Surjective g :=
  extendScalars_generators (iterateFrobenius D p n) M f hf

lemma frobeniusModule_finiteLength [IsLocalRing D] [IsNoetherianRing D]
    (hM : IsFiniteLength D M) (n : ℕ) : IsFiniteLength D (FrobeniusModule D p n M) := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := finiteLength_primary_annihilator hM
  exact finiteLength_of_primary_annihilator _ (by rw [Lech.CharP.frobeniusIdeal_radical,hI])
    (frobeniusModule_annihilator D p M I hIM n)
end Lech

end

end OAI
