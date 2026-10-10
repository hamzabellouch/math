import Mathlib
import OAI.RingTheory.Multiplicity.BicomplexEuler
import OAI.RingTheory.Multiplicity.CartierQuotientDevissage

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

abbrev thickeningZ (N : ℕ) := CartierQuotient.quotient (I^N) (cechZ I z hz m)
abbrev firstZ := CartierQuotient.quotient I (cechZ I z hz m)

def firstZIso : firstZ I z hz m ≅ exceptionalZ I z hz m := exceptionalCechZIso I z hz m

lemma cechZ_bounded (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) : IsZero ((cechZ I z hz m).X q) := by
  apply FiniteModuleCech.positiveZ_bounded (cechDiagram I z hz m) q
  simp only [Fintype.card_fin]
  omega

lemma thickeningZ_bounded (N : ℕ) (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((thickeningZ I z hz m N).X q) :=
  (TensorIdeal.quotientFunctor (I^N)).map_isZero (cechZ_bounded I z hz m q hq)

lemma thickeningZ_homology_bounded (N : ℕ) (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((thickeningZ I z hz m N).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (thickeningZ_bounded I z hz m N q hq)

lemma firstZ_homology_bounded (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((firstZ I z hz m).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((TensorIdeal.quotientFunctor I).map_isZero (cechZ_bounded I z hz m q hq))

lemma thickeningZ_zero : IsZero (thickeningZ I z hz m 0) := by
  apply FiniteComplex.isZero_of_X
  intro q
  change IsZero (ModuleCat.of R (((cechZ I z hz m).X q) ⧸
    (I^0 • (⊤ : Submodule R ((cechZ I z hz m).X q)))))
  rw [show I^0 • (⊤ : Submodule R ((cechZ I z hz m).X q)) = ⊤ from by
    rw [pow_zero,Ideal.one_eq_top,Submodule.top_smul]]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

variable (hgen : Ideal.span (Set.range z)=I)
def thickeningShortComplex (N : ℕ) :=
  CartierQuotient.shortComplex I (cechInclusionZ I z hz m 1)
    (fun q => by simpa only [pow_one] using cechInclusionZ_range I z hz m hgen 1 q) N

lemma thickeningShortComplex_exact (N : ℕ) : (thickeningShortComplex I z hz m hgen N).ShortExact :=
  CartierQuotient.shortComplex_exact I _ _ (cechInclusionZ_injective I z hz m 1) N

variable [LinearOrder (Chart n)] (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma firstZ_finite (q : ℤ) : ell.finiteClass ((firstZ I z hz m).homology q) :=
  ell.finiteClass.prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (firstZIso I z hz m)).symm
    (exceptionalZ_finite I z hz m hgen ell hds hmu ha q)

include hgen hds hmu ha in
lemma thickeningZ_finite (N : ℕ) (q : ℤ) : ell.finiteClass ((thickeningZ I z hz m N).homology q) := by
  induction N generalizing m with
  | zero => exact ell.finiteClass.prop_of_isZero ((homologyFunctor _ _ q).map_isZero (thickeningZ_zero I z hz m))
  | succ N ih =>
      have hs := thickeningShortComplex_exact I z hz m hgen N
      exact ell.finiteClass.prop_X₂_of_exact (hs.homology_exact₂ q) (ih (raise m 1))
        (firstZ_finite I z hz m hgen ell hds hmu ha q)

include hgen hds hmu ha in
lemma firstZ_euler : finiteHomologyEuler ell (firstZ I z hz m) 0 n=
    finiteHomologyEuler ell (exceptionalZ I z hz m) 0 n :=
  finiteHomologyEuler_iso ell _ _ (firstZIso I z hz m)
    (fun q => (firstZ_finite I z hz m hgen ell hds hmu ha q).1) 0 n

omit [LinearOrder (Chart n)] in
lemma raise_raise (m : Fin n → ℤ) (a b : ℕ) : raise (raise m a) b=raise m (a+b) := by
  funext j
  simp only [raise_apply,Nat.cast_add]
  ring

include hgen hds hmu ha in
 
theorem thickeningZ_euler (N : ℕ) :
    finiteHomologyEuler ell (thickeningZ I z hz m N) 0 n=
      ∑ j∈Finset.range N,finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  induction N generalizing m with
  | zero =>
      simp only [Finset.range_zero,Finset.sum_empty]
      unfold finiteHomologyEuler
      apply Finset.sum_eq_zero
      intro j hj
      have hz0 : IsZero ((thickeningZ I z hz m 0).homology (0+j)) :=
        (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (0+(j:ℤ))).map_isZero (thickeningZ_zero I z hz m)
      rw [ell.realValue_zero hz0,mul_zero]
  | succ N ih =>
      have hs := thickeningShortComplex_exact I z hz m hgen N
      have he := finiteHomologyEuler_additive ell _ hs 0 n
        (thickeningZ_finite I z hz (raise m 1) hgen ell hds hmu ha N)
        (thickeningZ_finite I z hz m hgen ell hds hmu ha (N+1))
        (firstZ_finite I z hz m hgen ell hds hmu ha)
        (firstZ_homology_bounded I z hz m _ (Or.inl (by omega)))
        (thickeningZ_homology_bounded I z hz (raise m 1) N _ (Or.inr (by omega)))
      change finiteHomologyEuler ell (thickeningZ I z hz m (N+1)) 0 n=
        finiteHomologyEuler ell (thickeningZ I z hz (raise m 1) N) 0 n+
          finiteHomologyEuler ell (firstZ I z hz m) 0 n at he
      rw [he,ih,firstZ_euler I z hz m hgen ell hds hmu ha,Finset.sum_range_succ']
      congr 1

end Lech.ReesRoot

end

end OAI
