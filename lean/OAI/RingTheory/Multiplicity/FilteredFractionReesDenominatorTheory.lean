import Mathlib
import OAI.RingTheory.Multiplicity.FilteredFractionReesDenominator

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.FilteredFraction
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hv : v ∈ I^e) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hwc hdeg in
lemma reesDenominator_mul : reesDenominator I hw * reesDenominator I hc =
    reesDenominator I hv := by
  apply Subtype.ext
  change Polynomial.monomial d w * Polynomial.monomial k c=Polynomial.monomial e v
  rw [Polynomial.monomial_mul_monomial,hwc,hdeg]

lemma reesAmbient_naturality :
    (reesAmbient I hv).comp (TwistedLocalization.ambientTo (R := R)
      (show reesDenominator I hw ∣ reesDenominator I hv from
        ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)) =
    (TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)).comp
      (reesAmbient I hw) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (reesDenominator I hw))
  ext a
  change reesAmbient I hv (TwistedLocalization.ambientTo (R := R)
    (show reesDenominator I hw ∣ reesDenominator I hv from
      ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)
    (algebraMap (reesAlgebra I) _ a)) =
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
      (reesAmbient I hw (algebraMap (reesAlgebra I) _ a))
  simp only [TwistedLocalization.ambientTo_algebraMap,reesAmbient_algebraMap]

 
def reesRestrict (t : ℕ) :=
  TwistedLocalization.pieceTo (R := R) (reesGrade I) (reesDenominator_mem I hw)
    (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc hwc hdeg) hdeg t

lemma reesEquiv_restrict (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    reesEquiv I hv t (reesRestrict I hw hv hc hwc hdeg t x) =
      restrict I hw hc hwc hdeg t (reesEquiv I hw t x) := by
  apply Subtype.ext
  exact AlgHom.congr_fun (reesAmbient_naturality I hw hv hc hwc hdeg) x.val

attribute [local irreducible] TwistedLocalization.piece quotientGraded TwistedLocalization.ambientMap TwistedLocalization.ambientTo
lemma quotientDenominator_mem {a : R} {n : ℕ} (ha : a ∈ I^n) :
    quotientGraded I (reesDenominator I ha) ∈ SourceGraded.targetGrade I n := by
  rw [quotientGraded_apply]
  exact ⟨reesDenominator I ha,reesDenominator_mem I ha,rfl⟩

 
def exceptionalRestrict (t : ℕ) :=
  TwistedLocalization.imagePieceTo (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I)
    (reesDenominator_mem I hw) (reesDenominator_mem I hc)
    (reesDenominator_mul I hw hv hc hwc hdeg) hdeg t

lemma quotientTwist_restrict (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    quotientTwist I hv t (reesRestrict I hw hv hc hwc hdeg t x) =
      exceptionalRestrict I hw hv hc hwc hdeg t (quotientTwist I hw t x) := by
  apply Subtype.ext
  have hn := TwistedLocalization.ambientMap_naturality (R := R)
    (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (SourceGraded.targetGrade I) (quotientGraded I) (quotientGraded_smul I)
    (f := reesDenominator I hw) (q := reesDenominator I hv)
    (show reesDenominator I hw ∣ reesDenominator I hv from
      ⟨reesDenominator I hc,(reesDenominator_mul I hw hv hc hwc hdeg).symm⟩)
  exact AlgHom.congr_fun hn x.val


lemma layerMap_naturality (t : ℕ) (x : piece I w d t) :
    layerMap I hv t (restrict I hw hc hwc hdeg t x) =
      exceptionalRestrict I hw hv hc hwc hdeg t (layerMap I hw t x) := by
  obtain ⟨y,rfl⟩ := (reesEquiv I hw t).surjective x
  rw [←reesEquiv_restrict I hw hv hc hwc hdeg]
  change quotientTwist I hv t ((reesEquiv I hv t).symm
    (reesEquiv I hv t (reesRestrict I hw hv hc hwc hdeg t y))) =
    exceptionalRestrict I hw hv hc hwc hdeg t
      (quotientTwist I hw t ((reesEquiv I hw t).symm (reesEquiv I hw t y)))
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  exact quotientTwist_restrict I hw hv hc hwc hdeg t y
end Lech.FilteredFraction


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.quotientGraded

lemma exceptionalTermEquiv_restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : FilteredFraction.exceptionalPiece I
      (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t) :
    exceptionalTermEquiv I z hz v t
      (FilteredFraction.exceptionalRestrict I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) (v\s))
        (GradedChart.denominator_mul_sdiff z hsv)
        (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x) =
    ImageCech.restrict (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X (MvPolynomial.isHomogeneous_X (R ⧸ I)) hsv t
      (exceptionalTermEquiv I z hz s t x) := by
  unfold exceptionalTermEquiv FilteredFraction.exceptionalRestrict TwistedLocalization.imagePieceTo ImageCech.restrict
  apply TwistedLocalization.pieceCongr_pieceTo


lemma filteredReduction_naturality {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : FilteredCech.term I z t s) :
    filteredReduction I z hz v t
      (LocalizationCech.restrict z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) hsv x) =
    ImageCech.restrict (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X (MvPolynomial.isHomogeneous_X (R ⧸ I)) hsv t
      (filteredReduction I z hz s t x) := by
  change exceptionalTermEquiv I z hz v t
    (FilteredFraction.layerMap I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v) t
      (FilteredFraction.restrict I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) (v\s))
        (GradedChart.denominator_mul_sdiff z hsv)
        (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x)) = _
  rw [FilteredFraction.layerMap_naturality I
    (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)
    (FilteredCech.denominator_mem I z (coordinate_mem I z hz) v)]
  exact exceptionalTermEquiv_restrict I z hz hsv t _
end Lech.SourceGraded


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

lemma inclusion_refl (t : ℕ) : inclusion I z hz (le_refl t)=𝟙 (complex I z hz t) := by
  ext n x
  rfl

lemma inclusion_comp {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    inclusion I z hz hst ≫ inclusion I z hz hrs = inclusion I z hz (hrs.trans hst) := by
  ext n x
  rfl

instance inclusion_mono {s t : ℕ} (hst : s ≤ t) : Mono (inclusion I z hz hst) := by
  apply mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  exact LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
    (fun _ => FilteredFraction.antitone I _ _ hst) n
end Lech.FilteredCech

open scoped BigOperators
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

noncomputable def realValue (M : ModuleCat.{u} R) : ℝ := (ℓ.value M).toReal

lemma additive_real {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hM : ℓ.finiteClass S.X₂) :
    ℓ.realValue S.X₂ = ℓ.realValue S.X₁ + ℓ.realValue S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h₁ := ℓ.finiteClass.prop_of_mono S.f hM
  have h₃ := ℓ.finiteClass.prop_of_epi S.g hM
  exact (congrArg ENNReal.toReal (ℓ.additive hS hM.1)).trans
    (ENNReal.toReal_add h₁.2 h₃.2)

lemma realValue_zero {M : ModuleCat.{u} R} (hM : IsZero M) :
    ℓ.realValue M = 0 := by simp [realValue, ℓ.zero hM]

lemma exact_real_image_sum (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) (hM : ℓ.finiteClass S.X₂) :
    ℓ.realValue S.X₂ = ℓ.realValue (image S.f) + ℓ.realValue (image S.g) := by
  let T := ShortComplex.mk (Limits.image.ι S.f) S.g (image_ι_comp_eq_zero S.zero)
  have hT : T.Exact := T.exact_of_f_is_kernel hS.isLimitImage'
  let U := ShortComplex.mk T.f (factorThruImage T.g)
    (comp_factorThruImage_eq_zero T.zero)
  have hU : U.ShortExact :=
    { exact := U.exact_of_g_is_cokernel hT.isColimitImage
      mono_f := (inferInstance : Mono (Limits.image.ι S.f))
      epi_g := (inferInstance : Epi (factorThruImage T.g)) }
  exact ℓ.additive_real hU hM

end TorsionLength

lemma alternating_sum_pairs (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * (a i + a (i + 1)) =
      a 0 + (-1 : ℝ) ^ n * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring


lemma exact_euler_zero (ℓ : TorsionLength I)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l : ℤ) (n : ℕ)
    (hex : ∀ i, F.ExactAt i) (hfin : ∀ i, ℓ.finiteClass (F.X i))
    (hl : IsZero (F.X (l - 1))) (hr : IsZero (F.X (l + n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * ℓ.realValue (F.X (l + i)) = 0 := by
  let a (i : ℕ) := ℓ.realValue (image (F.d (l + i - 1) (l + i)))
  have hi (i : ℕ) : ℓ.realValue (F.X (l + i)) = a i + a (i + 1) := by
    let S := ShortComplex.mk (F.d (l + i - 1) (l + i))
      (F.d (l + i) (l + i + 1)) (F.d_comp_d _ _ _)
    have hS : S.Exact := (F.exactAt_iff' (l + i - 1) (l + i) (l + i + 1)
      (by simp) (by simp)).mp (hex (l + i))
    have h := ℓ.exact_real_image_sum S hS (hfin _)
    have imagesCongr (j j' k k' : ℤ) (hj : j = j') (hk : k = k') :
        ℓ.realValue (image (F.d j k)) = ℓ.realValue (image (F.d j' k')) := by
      subst j'; subst k'; rfl
    exact h.trans (congrArg (ℓ.realValue (image S.f) + ·)
      (imagesCongr _ _ _ _ (by omega) (by omega)))
  simp_rw [hi]
  rw [alternating_sum_pairs a n]
  have ha₀ : a 0 = 0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_epi (factorThruImage (F.d (l + 0 - 1) (l + 0)))
    simpa using hl
  have ha₁ : a (n + 1) = 0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_mono (Limits.image.ι (F.d (l + (n + 1) - 1) (l + (n + 1))))
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hr
  rw [ha₀, ha₁, mul_zero, add_zero]

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
 

def finiteHomologyEuler (K : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N+1),(-1:ℝ)^i*ℓ.realValue (K.homology (m+i))
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
lemma homology_length_defect (j : ℤ)
    (h₁ : ℓ.finiteClass (S.X₁.homology j))
    (h₂ : ℓ.finiteClass (S.X₂.homology j))
    (h₃ : ℓ.finiteClass (S.X₃.homology j)) :
    ℓ.realValue (S.X₁.homology j)-ℓ.realValue (S.X₂.homology j)+ℓ.realValue (S.X₃.homology j)=
      ℓ.realValue (image (hS.δ (j-1) j (by change j-1+1=j;omega)))+
      ℓ.realValue (image (hS.δ j (j+1) rfl)) := by
  have h1 := ℓ.exact_real_image_sum _ (hS.homology_exact₁ (j-1) j (by change j-1+1=j;omega)) h₁
  have h2 := ℓ.exact_real_image_sum _ (hS.homology_exact₂ j) h₂
  have h3 := ℓ.exact_real_image_sum _ (hS.homology_exact₃ j (j+1) rfl) h₃
  dsimp only at h1 h2 h3
  linarith
include hS in
 

theorem finiteHomologyEuler_additive (m : ℤ) (N : ℕ)
    (h₁ : ∀ i,ℓ.finiteClass (S.X₁.homology i))
    (h₂ : ∀ i,ℓ.finiteClass (S.X₂.homology i))
    (h₃ : ∀ i,ℓ.finiteClass (S.X₃.homology i))
    (hl : IsZero (S.X₃.homology (m-1))) (hr : IsZero (S.X₁.homology (m+N+1))) :
    finiteHomologyEuler ℓ S.X₂ m N=finiteHomologyEuler ℓ S.X₁ m N+finiteHomologyEuler ℓ S.X₃ m N := by
  let a (i : ℕ) := ℓ.realValue (image (hS.δ (m+i-1) (m+i) (by change m+i-1+1=m+i;omega)))
  have hi (i : ℕ) : ℓ.realValue (S.X₁.homology (m+i))-ℓ.realValue (S.X₂.homology (m+i))+
      ℓ.realValue (S.X₃.homology (m+i))=a i+a (i+1) := by
    rw [homology_length_defect ℓ S hS (m+i) (h₁ _) (h₂ _) (h₃ _)]
    have hδ (j j' k k' : ℤ) (hjk : j+1=k) (hjk' : j'+1=k')
        (hj : j=j') (hk : k=k') :
        ℓ.realValue (image (hS.δ j k hjk))=ℓ.realValue (image (hS.δ j' k' hjk')) := by
      subst j';subst k';rfl
    exact congrArg (a i + ·) (hδ _ _ _ _ rfl _ (by push_cast;omega) (by push_cast;omega))
  have ha₀ : a 0=0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_epi (factorThruImage (hS.δ (m+0-1) (m+0) (by change m+0-1+1=m+0;omega)))
    simpa using hl
  have ha₁ : a (N+1)=0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_mono (Limits.image.ι (hS.δ (m+(N+1)-1) (m+(N+1)) (by change m+(N+1)-1+1=m+(N+1);omega)))
    simpa [Nat.cast_add,Nat.cast_one,add_assoc] using hr
  have he : finiteHomologyEuler ℓ S.X₁ m N-finiteHomologyEuler ℓ S.X₂ m N+
      finiteHomologyEuler ℓ S.X₃ m N=0 := by
    calc
      _=∑ i ∈ Finset.range (N+1),(-1:ℝ)^i*(ℓ.realValue (S.X₁.homology (m+i))-
          ℓ.realValue (S.X₂.homology (m+i))+ℓ.realValue (S.X₃.homology (m+i))) := by
        simp only [finiteHomologyEuler,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      _=a 0+(-1:ℝ)^N*a (N+1) := by
        simp_rw [hi]
        exact alternating_sum_pairs a N
      _=0 := by rw [ha₀,ha₁,mul_zero,add_zero]
  linarith
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
lemma finiteHomologyEuler_homologyIso (e : ∀ q,K.homology q ≅ L.homology q)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg ENNReal.toReal (ℓ.eq_of_iso (e (m+i)) (hK _) ((powerTorsion I).prop_of_iso (e (m+i)) (hK _)))
lemma finiteHomologyEuler_iso (e : K ≅ L)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N :=
  finiteHomologyEuler_homologyIso ℓ K L (fun q => (homologyFunctor _ _ q).mapIso e) hK m N
lemma finiteHomologyEuler_zero (hK : ∀ q,IsZero (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [ℓ.realValue_zero (hK _),mul_zero]
end Lech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u v
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable {C : Type v} [Category C] [Abelian C]
variable (T : CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [T.Additive]
variable (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
  (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) →
  ∀ j, ((S.map T).map (eval (ModuleCat.{u} R) (.up ℤ) j)).Splitting)
variable (a : ℤ) (w : ℕ)
include hT in
 

theorem euler_devissage (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hf : ∀ j q, ℓ.finiteClass ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology q))
    (hl : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology (a-1)))
    (hr : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology (a+w+1))) :
    finiteHomologyEuler ℓ (T.obj F) a w =
      ∑ k ∈ Finset.range N,finiteHomologyEuler ℓ (T.obj
        ((single C (.up ℤ) (m+k)).obj (F.X (m+k)))) a w := by
  induction N generalizing F with
  | zero =>
    rw [Finset.range_zero,Finset.sum_empty]
    apply finiteHomologyEuler_zero
    intro q
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
      (T.map_isZero (isZero_of_X F (fun j => hb j (by omega))))
  | succ N ih =>
    let n : ℤ := m+N
    have hn : ∀ j,n<j → IsZero (F.X j) := fun j hj => hb j (by dsimp [n] at hj;omega)
    let D := dropTop F n hn
    have hbD : ∀ j,j < m ∨ m+(N:ℤ)≤j → IsZero (D.X j) := by
      intro j hj
      by_cases hjn : j=n
      · subst j;exact dropTop_X_top F n hn
      · exact (hb j (by dsimp [n] at hjn;omega)).of_iso (dropTopXIso F n hn j hjn).symm
    have hpiece (P : ObjectProperty (ModuleCat.{u} R)) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
        (q : ℤ) (h : ∀ j,P ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology q))
        (j : ℤ) : P ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology q) := by
      by_cases hjn : j=n
      · subst j
        exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
          (T.map_isZero ((single C (.up ℤ) n).map_isZero (dropTop_X_top F n hn))))
      · exact P.prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
          (T.mapIso ((single C (.up ℤ) j).mapIso (dropTopXIso F n hn j hjn)))) (h j)
    have hfD : ∀ j q,ℓ.finiteClass ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology q) :=
      fun j q => hpiece ℓ.finiteClass q (fun t => hf t q) j
    have hlD : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology (a-1)) :=
      hpiece (IsZero (C:=ModuleCat.{u} R)) (a-1) hl
    have hrD : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology (a+w+1)) :=
      hpiece (IsZero (C:=ModuleCat.{u} R)) (a+w+1) hr
    have hfiniteF (q : ℤ) : ℓ.finiteClass ((T.obj F).homology q) :=
      homology_devissage_to ℓ.finiteClass T hT m (N+1) F q hb (fun j => hf j q)
    have hfiniteD (q : ℤ) : ℓ.finiteClass ((T.obj D).homology q) :=
      homology_devissage_to ℓ.finiteClass T hT m N D q hbD (fun j => hfD j q)
    have hleftD : IsZero ((T.obj D).homology (a-1)) :=
      homology_devissage_to (IsZero (C:=ModuleCat.{u} R)) T hT m N D (a-1) hbD hlD
    have hs : ((topShortComplex F n hn).map T).ShortExact :=
      shortExact_of_degreewise_shortExact _ (fun j => (hT _ (topSplitting F n hn) j).shortExact)
    have he := finiteHomologyEuler_additive ℓ ((topShortComplex F n hn).map T) hs a w
      (hf n) hfiniteF hfiniteD hleftD (hr n)
    change finiteHomologyEuler ℓ (T.obj F) a w =
      finiteHomologyEuler ℓ (T.obj ((single C (.up ℤ) n).obj (F.X n))) a w+
        finiteHomologyEuler ℓ (T.obj D) a w at he
    rw [he,ih D hbD hfD hlD hrD,Finset.sum_range_succ,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : m+(k:ℤ)≠n := by dsimp [n];have := Finset.mem_range.mp hk;omega
    apply (finiteHomologyEuler_iso ℓ _ _
      (T.mapIso ((single C (.up ℤ) (m+k)).mapIso (dropTopXIso F n hn (m+k) hkn)))
      (fun q => (hf (m+k) q).1) a w).symm
end Lech.FiniteComplex


namespace Lech.FiniteCoverCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w}
abbrev Row (n : ℕ) := (Fin n → ι) → M

def delta (n : ℕ) : Row M (ι := ι) n →ₗ[R] Row M (ι := ι) (n+1) where
  toFun f a := ∑ i : Fin (n+1),(-1:R)^i.val • f (a ∘ i.succAbove)
  map_add' _ _ := by ext a;simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext a
    simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
def extra (j : ι) (n : ℕ) : Row M (ι := ι) (n+1) →ₗ[R] Row M (ι := ι) n where
  toFun f a := f (Fin.cons j a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma delete_insert_zero {n : ℕ} (j : ι) (a : Fin n → ι) :
    Fin.cons j a ∘ (0:Fin (n+1)).succAbove=a := by funext i;simp
lemma delete_insert_succ {n : ℕ} (j : ι) (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    Fin.cons j a ∘ i.succ.succAbove=Fin.cons j (a ∘ i.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]
lemma extra_delta (j : ι) (n : ℕ) (f : Row M (ι := ι) (n+1)) :
    extra R M j (n+1) (delta R M (n+1) f)+delta R M n (extra R M j n f)=f := by
  ext a
  change (∑ i : Fin (n+2),(-1:R)^i.val • f (Fin.cons j a ∘ i.succAbove))+
    (∑ i : Fin (n+1),(-1:R)^i.val • f (Fin.cons j (a ∘ i.succAbove)))=f a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,delete_insert_zero,Fin.val_succ,
    pow_succ,delete_insert_succ,mul_neg_one,neg_smul,Finset.sum_neg_distrib]
  abel
lemma delta_square (n : ℕ) (f : Row M (ι := ι) n) : delta R M (n+1) (delta R M n f)=0 := by
  induction n with
  | zero =>
    ext a
    have hf (b : Fin 0 → ι) : f b=f Fin.elim0 := congrArg f (Subsingleton.elim _ _)
    simp [delta,Fin.sum_univ_two,hf]
  | succ n ih =>
    have hh (j : ι) : extra R M j (n+2) (delta R M (n+2) (delta R M (n+1) f))=0 := by
      have h₁ := extra_delta R M j (n+1) (delta R M (n+1) f)
      have h₂ := congrArg (delta R M (n+1)) (extra_delta R M j n f)
      rw [map_add,ih,add_zero] at h₂
      rw [h₂] at h₁
      exact add_right_cancel (h₁.trans (zero_add _).symm)
    ext a
    have he := congrFun (hh (a 0)) (fun i => a i.succ)
    change delta R M (n+2) (delta R M (n+1) f) (Fin.cons (a 0) (Fin.tail a))=0 at he
    rw [Fin.cons_self_tail] at he
    exact he

variable [Fintype ι] [DecidableEq ι]
def intersection {n : ℕ} (a : Fin n → ι) : Finset ι := Finset.univ.image a
omit [Fintype ι] in
lemma intersection_delete {n : ℕ} (a : Fin (n+1) → ι) (i : Fin (n+1)) :
    intersection (a ∘ i.succAbove) ⊆ intersection a := by
  intro j hj
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨i.succAbove k,Finset.mem_univ _,rfl⟩
omit [Fintype ι] in
lemma intersection_cons {n : ℕ} (j : ι) (a : Fin n → ι) :
    intersection (Fin.cons j a)=insert j (intersection a) := by
  ext i
  simp only [intersection,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨k,hk⟩
    revert hk
    refine Fin.cases ?_ (fun k => ?_) k
    · intro hk;left;exact hk.symm
    · intro hk;right;exact ⟨k,hk⟩
  · rintro (rfl|⟨k,rfl⟩)
    · exact ⟨0,Fin.cons_zero _ _⟩
    · exact ⟨k.succ,Fin.cons_succ _ _ _⟩
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def cochains (n : ℕ) : Submodule R (Row M (ι := ι) n) where
  carrier := {f | ∀ a,f a∈F (intersection a)}
  zero_mem' _ := (F _).zero_mem
  add_mem' hf hg a := (F _).add_mem (hf a) (hg a)
  smul_mem' r _ hf a := (F _).smul_mem r (hf a)
include hF in
omit [Fintype ι] in
lemma delta_mem (n : ℕ) {f : Row M (ι := ι) n} (hf : f∈cochains R M F n) :
    delta R M n f∈cochains R M F (n+1) := by
  intro a
  change (∑ i : Fin (n+1),(-1:R)^i.val • f (a ∘ i.succAbove))∈F (intersection a)
  apply (F _).sum_mem
  intro i _
  exact (F _).smul_mem _ (hF (intersection_delete a i) (hf _))
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
  (hclear : ∀ (s : Finset ι) (j : ι) (x : M), x∈F (insert j s) → ∃ m : ℕ,q j^m • x∈F s)
include hclear in
lemma uniform_clear (n : ℕ) (f : cochains R M F (n+1)) :
    ∃ N : ℕ,∀ (j : ι) (a : Fin n → ι),q j^N • f.val (Fin.cons j a)∈F (intersection a) := by
  choose m hm using fun (p : ι × (Fin n → ι)) =>
    hclear (intersection p.2) p.1 (f.val (Fin.cons p.1 p.2)) (by
      rw [←intersection_cons];exact f.property _)
  let N := Finset.univ.sup m
  refine ⟨N,fun j a => ?_⟩
  have hn : m (j,a)≤N := Finset.le_sup (Finset.mem_univ _)
  rw [←Nat.sub_add_cancel hn,pow_add,mul_smul]
  exact (F _).smul_mem _ (hm (j,a))
include hq in
omit [DecidableEq ι] in
lemma partition (N : ℕ) : ∃ c : ι → R,∑ j,c j*(q j)^N=1 := by
  have hp : Ideal.span (Set.range (fun j => q j^N))=⊤ := by
    simpa only [←Set.range_comp,Function.comp_def] using (Ideal.span_pow_eq_top (Set.range q) hq N)
  have hm := (Ideal.eq_top_iff_one _).mp hp
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm
  exact ⟨c,hc⟩
include hq hclear in
 

theorem exact (n : ℕ) (f : cochains R M F (n+1)) (hf : delta R M (n+1) f.val=0) :
    ∃ g : cochains R M F n,delta R M n g.val=f.val := by
  obtain ⟨N,hN⟩ := uniform_clear R M F q hclear n f
  obtain ⟨c,hc⟩ := partition R q hq N
  let g : Row M (ι := ι) n := ∑ j,c j • (q j^N • extra R M j n f.val)
  have hg : g∈cochains R M F n := by
    intro a
    change (∑ j,c j • (q j^N • extra R M j n f.val)) a∈F (intersection a)
    simp only [Finset.sum_apply,Pi.smul_apply]
    exact (F _).sum_mem fun j _ => (F _).smul_mem _ (hN j a)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R M n (extra R M j n f.val)=f.val := by
    have h := extra_delta R M j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,map_smul,hj,smul_smul,←Finset.sum_smul,hc,one_smul]
end Lech.FiniteCoverCech

end

end OAI
