import Mathlib
import OAI.RingTheory.Multiplicity.DuttaData
import OAI.RingTheory.Multiplicity.ProjectiveGhost

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct ChangeOfRings
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

instance extendScalars_additive (φ : R →+* S) : (ModuleCat.extendScalars φ).Additive where
  map_add := by
    intros M N f g
    let := φ.toAlgebra
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add _ _

lemma extendScalars_map_smul (φ : R →+* S) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : R) :
    (ModuleCat.extendScalars φ).map (x • f) =
      φ x • (ModuleCat.extendScalars φ).map f := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := φ.toAlgebra
  change (1:S) ⊗ₜ[R] (x • f m) = φ x • ((1:S) ⊗ₜ[R] (f m))
  rw [TensorProduct.tmul_smul]
  rfl

lemma extendScalars_complex_smul (φ : R →+* S)
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (f : F ⟶ G) (x : R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map (x • f) =
      φ x • ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f := by
  ext i : 1
  exact extendScalars_map_smul φ (f.f i) x

def extendScalars_nullhomotopy (φ : R →+* S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (φ x • 𝟙 (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F)) 0 := by
  have H' := (ModuleCat.extendScalars φ).mapHomotopy H
  rw [extendScalars_complex_smul,CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_zero] at H'
  exact H' 

def frobenius_nullhomotopy (p : ℕ) [Fact p.Prime] [CharP R p]
    (n a : ℕ) (F : CochainComplex (ModuleCat.{u} R) ℤ) (x : R)
    (H : Homotopy (x^a • 𝟙 F) 0) :
    Homotopy (x^(a*(p^n)) • 𝟙 (frobeniusComplex R p n F)) 0 := by
  simp only [frobeniusComplex]
  have h := extendScalars_nullhomotopy (iterateFrobenius R p n) F (x^a) H
  have he : iterateFrobenius R p n (x^a) = x^(a*(p^n)) := by
    rw [iterateFrobenius_def, pow_mul]
  rw [he] at h
  exact h
end Lech

end

end OAI
