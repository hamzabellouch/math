import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredComplex

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 
def subcomplexNullHomotopy {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (T : ∀ p, Submodule R (L.X p))
    (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom)
    (hT : ∀ p q, T p ≤ (T q).comap (L.d p q).hom)
    (f : K ⟶ L) (hf : ∀ p, P p ≤ (T p).comap (f.f p).hom)
    (H : Homotopy f 0) (hH : ∀ p q, P p ≤ (T q).comap (H.hom p q).hom) :
    Homotopy (subcomplexMap K L P T hP hT f hf) 0 where
  hom p q := ModuleCat.ofHom (((H.hom p q).hom.comp (P p).subtype).codRestrict (T q)
    (fun x => hH p q x.property))
  zero p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (H.hom p q).hom x.val=0
    rw [H.zero p q hpq]
    rfl
  comm p := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun g : K.X p ⟶ L.X p => g.hom x.val) (H.comm p)

lemma order_mono (h s : ℕ) : Monotone (order h s) := by
  intro p q hpq
  unfold order
  apply Nat.mul_le_mul_right
  exact Int.toNat_le_toNat (by omega)

variable (I : Ideal R)
lemma linear_decreases {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {a b : ℕ} (hab : b ≤ a) :
    I^a • (⊤ : Submodule R M) ≤ (I^b • (⊤ : Submodule R N)).comap f :=
  (Submodule.smul_top_le_comap_smul_top (I^a) f).trans
    (Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  {Q Q' : ModuleCat.{u} R} (inc : Q ⟶ Q')

 

def coefficientNullHomotopy (H : Homotopy (tensorMap F inc) 0) :
    Homotopy (map I F h s hd inc) 0 :=
  subcomplexNullHomotopy (tensorComplex F Q) (tensorComplex F Q')
    (term I F h s Q) (term I F h s Q')
    (term_d I F h s hd Q) (term_d I F h s hd Q') (tensorMap F inc)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F inc).f p).hom)
    H (by
      intro p q
      by_cases hpq : (ComplexShape.up ℤ).Rel q p
      · apply linear_decreases
        apply order_mono
        change q+1=p at hpq
        omega
      · rw [H.zero p q hpq]
        intro x hx
        exact (term I F h s Q' q).zero_mem)

end Lech.IdealFiltered

end

end OAI
