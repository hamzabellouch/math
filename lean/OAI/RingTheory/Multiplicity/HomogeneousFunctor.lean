import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousZeroPiece

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A),g (r • a)=r • g a)
attribute [local instance] awayAddCommGroup

instance awayAlgebra (element : A) : Algebra R (Away G element) :=
  Algebra.ofModule
    (fun scalar left right => by
      apply val_injective (Submonoid.powers element)
      simp only [val_mul, val_smul, smul_mul_assoc])
    (fun scalar left right => by
      apply val_injective (Submonoid.powers element)
      simp only [val_mul, val_smul, mul_smul_comm])

def awayAlg (f : A) : Away G f →ₐ[R] Away H (g f) where
  __ := Away.map g f
  commutes' r := by
    change awayMap G H g hg f (algebraMap R (Away G f) r) = _
    rw [Algebra.algebraMap_eq_smul_one,map_smul]
    change r • (Away.map g f) 1 = _
    rw [map_one,Algebra.algebraMap_eq_smul_one]

lemma awayAlg_surjective {f : A} {d : ℕ} (hf : f ∈ G d)
    (hs : Function.Surjective g) : Function.Surjective (awayAlg G H g hg f) :=
  awayMap_surjective G H g hg hf hs

lemma awayAlg_piece (f : A) : (awayAlg G H g hg f).toLinearMap = awayMap G H g hg f := rfl

lemma awayMap_one (f : A) : awayMap G H g hg f 1 = 1 :=
  map_one (Away.map g f)
lemma awayMap_mul (f : A) (a b : Away G f) :
    awayMap G H g hg f (a*b) = awayMap G H g hg f a * awayMap G H g hg f b :=
  map_mul (Away.map g f) a b
lemma awayMap_mk {f : A} {d : ℕ} (hf : f∈G d) (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    awayMap G H g hg f (Away.mk G hf j a ha) =
      Away.mk H (Graded.map_mem g hf) j (g a) (Graded.map_mem g ha) :=
  Away.map_mk g f hf j a ha

 

def awayCongr {f q : A} (e : f=q) : Away G f ≃ₐ[R] Away G q := by
  subst q
  exact AlgEquiv.refl
lemma awayCongr_mk {f q : A} (e : f=q) {d : ℕ} (hf : f∈G d) (hq : q∈G d)
    (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    awayCongr G e (Away.mk G hf j a ha)=Away.mk G hq j a ha := by
  subst q
  rfl

lemma awayCongr_symm_mk {f q : A} (e : f=q) {d : ℕ} (hf : f∈G d) (hq : q∈G d)
    (j : ℕ) (a : A) (ha : a∈G (j • d)) :
    (awayCongr G e).symm (Away.mk G hq j a ha)=Away.mk G hf j a ha := by
  subst q
  rfl
end Lech.Homogeneous

namespace Lech
lemma linearEquiv_mem_ideal_smul_top_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) (x : M) :
    e x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have hmap : Submodule.map e.toLinearMap (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  rw [←hmap]
  constructor
  · rintro ⟨y,hy,he⟩
    exact e.injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩
end Lech

end

end OAI
