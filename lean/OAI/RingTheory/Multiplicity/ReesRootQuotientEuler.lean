import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootQuotient
import OAI.RingTheory.Multiplicity.ReesRootThickeningEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

lemma enlargedAt_row_bounded (p q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero (((enlargedAt I z hz F h s hd m).X p).X q) := by
  let Q := (cechZ I z hz m).X q
  exact @IsZero.of_mono (ModuleCat.{u} R) _ _ _ _
    ((IdealFiltered.ambientInclusion I F h s hd Q).f p)
    (IdealFiltered.ambientInclusion_mono I F h s hd Q p)
    ((tensorLeft (F.X p)).map_isZero (cechZ_bounded I z hz m q hq))

lemma total_rectangle_zero (K : TotalGhost.Bic (R:=R))
    (hb : ∀ p q,p < -(h:ℤ) ∨ 0<p → IsZero ((K.X p).X q))
    (hq : ∀ p q,q<0 ∨ (n:ℤ)<q → IsZero ((K.X p).X q))
    (t : ℤ) (ht : t < -(h:ℤ) ∨ (n:ℤ)<t) : IsZero ((K.total (.up ℤ)).X t) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply total.hom_ext
  intro p q hpq
  have hzero : IsZero ((K.X p).X q) := by
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact hb p q hp
    · exact hq p q (by change p+q=t at hpq; omega)
  exact hzero.eq_of_src _ _

variable (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
include hb in
lemma quotientAtTotal_bounded (q : ℤ) (hq : q < -(h:ℤ) ∨ (n:ℤ)<q) :
    IsZero (((quotientAt I z hz F h s hd m).total (.up ℤ)).homology q) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  apply total_rectangle_zero h _ _ _ q hq
  · intro p r hp
    exact (HomologicalComplex.eval _ _ r).map_isZero (quotientAt_isZero I z hz F h s hd m p (hb p hp))
  · exact quotientAt_row_bounded I z hz F h s hd m

include hb in
lemma enlargedAtTotal_bounded (q : ℤ) (hq : q < -(h:ℤ) ∨ (n:ℤ)<q) :
    IsZero (((enlargedAt I z hz F h s hd m).total (.up ℤ)).homology q) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact total_rectangle_zero h _
    (fun p r hp => enlargedAt_isZero I z hz F h s hd m p r (hb p hp))
    (enlargedAt_row_bounded I z hz F h s hd m) q hq

variable [LinearOrder (Chart n)] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))

include hgen hds hmu ha B hflat in
lemma quotientAt_row_finite (p q : ℤ) :
    ell.finiteClass (((quotientAt I z hz F h s hd m).X p).homology q) := by
  let := hflat p
  let K := thickeningZ I z hz m (IdealFiltered.order h s p)
  have hf := thickeningZ_finite I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p) q
  apply ell.finiteClass.prop_of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (quotientAtRowIso I z hz F h s hd m p))
  exact ⟨TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) K I q hf.1,
    TensorIdeal.tensorHomology_length_finite (F.X p) (b p) (B p) K I ell q hf.1 hf.2⟩

include hgen hds hmu ha B hflat in
lemma quotientAt_row_euler (p : ℤ) :
    finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).X p) 0 n=
      (b p:ℝ)*∑ j∈Finset.range (IdealFiltered.order h s p),
        finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  let := hflat p
  let K := thickeningZ I z hz m (IdealFiltered.order h s p)
  have hf (q : ℤ) := thickeningZ_finite I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p) q
  rw [←finiteHomologyEuler_iso ell _ _ (quotientAtRowIso I z hz F h s hd m p)
    (fun q => TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) K I q (hf q).1) 0 n]
  rw [←thickeningZ_euler I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p)]
  unfold finiteHomologyEuler
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := TensorIdeal.tensorHomology_length (F.X p) (b p) (B p) K I ell (0+j) (hf _).1
  change (-1:ℝ)^j*(ell.value _).toReal=_
  rw [he,nsmul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast]
  dsimp only [TorsionLength.realValue]
  ring

include hb hgen hds hmu ha B hflat in
lemma quotientAtTotal_finite (q : ℤ) :
    ell.finiteClass (((quotientAt I z hz F h s hd m).total (.up ℤ)).homology q) := by
  apply BicomplexTotal.devissage ell.finiteClass (-(h:ℤ)) (h+1) _ q
  · intro p hp
    exact quotientAt_isZero I z hz F h s hd m p (hb p (by omega))
  intro p
  exact ell.finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p q).symm
    (quotientAt_row_finite I z hz F h s hd m hgen ell hds hmu ha b B hflat p _)

include hb hgen hds hmu ha B hflat in
 
lemma quotientAtTotal_euler (N : ℕ) (hN : h+n≤N) :
    finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N=
      ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)*
        ∑ j∈Finset.range (IdealFiltered.order h s (-(h:ℤ)+k)),
          finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  rw [BicomplexTotal.euler_rows ell _ h n N hN
    (fun p hp => quotientAt_isZero I z hz F h s hd m p (hb p hp))
    (fun p q hq => ShortComplex.isZero_homology_of_isZero_X₂ _
      (quotientAt_row_bounded I z hz F h s hd m p q hq))
    (quotientAt_row_finite I z hz F h s hd m hgen ell hds hmu ha b B hflat)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [quotientAt_row_euler I z hz F h s hd m hgen ell hds hmu ha b B hflat,mul_assoc]

variable (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hb hgen hds hmu ha B hflat hp hfin hac in
 
theorem ambient_euler_additive (N : ℕ) (hN : h+n≤N) :
    finiteHomologyEuler ell ((unfilteredAt I z hz F m).total (.up ℤ)) (-(h:ℤ)) N=
      finiteHomologyEuler ell ((enlargedAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N+
      finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N := by
  exact finiteHomologyEuler_additive ell _
    (BicomplexTotal.total_shortExact _ (quotientShortComplex_exact I z hz F h s hd m)) (-(h:ℤ)) N
    (enlargedAtTotal_finite I z hz F h s hd m hgen hflat ell hds hmu ha b B hp hfin hb hac)
    (unfilteredTotal_finite I z hz F h m hgen ell hds hmu ha b B hflat hp hfin hb hac)
    (quotientAtTotal_finite I z hz F h s hd m hb hgen ell hds hmu ha b B hflat)
    (quotientAtTotal_bounded I z hz F h s hd m hb _ (Or.inl (by omega)))
    (enlargedAtTotal_bounded I z hz F h s hd m hb _ (Or.inr (by omega)))
end Lech.ReesRoot

end

end OAI
