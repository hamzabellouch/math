import Mathlib
import OAI.RingTheory.Multiplicity.RestrictedPolynomialImageCechComparisonHomology

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

section
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)


abbrev reesDenominator : reesAlgebra I := monomial I d ⟨w,hw⟩
lemma reesDenominator_mem : reesDenominator I hw ∈ reesGrade I d := ⟨⟨w,hw⟩,rfl⟩

 
def reesAmbient : Localization.Away (reesDenominator I hw) →ₐ[R] Localization.Away w := by
  letI : IsLocalization.Away ((evaluate I) (reesDenominator I hw)) (Localization.Away w) := by
    simpa only [reesDenominator,evaluate_monomial] using
      (inferInstance : IsLocalization.Away w (Localization.Away w))
  exact IsLocalization.Away.mapₐ _ _ (evaluate I) (reesDenominator I hw)

lemma reesAmbient_algebraMap (a : reesAlgebra I) :
    reesAmbient I hw (algebraMap (reesAlgebra I) (Localization.Away (reesDenominator I hw)) a) =
      algebraMap R (Localization.Away w) ((evaluate I) a) := by
  simp only [reesAmbient, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

lemma reesAmbient_fraction (t n : ℕ) (a : ↥(I^(n*d+t))) :
    reesAmbient I hw (TwistedLocalization.fraction (reesGrade I)
      (f := reesDenominator I hw) t n ⟨monomial I _ a,⟨a,rfl⟩⟩) = fraction I w d t n a := by
  have hd : reesAmbient I hw (algebraMap (reesAlgebra I)
      (Localization.Away (reesDenominator I hw)) ((reesDenominator I hw)^n)) =
      algebraMap R (Localization.Away w) (w^n) := by
    rw [reesAmbient_algebraMap,map_pow]
    simp only [reesDenominator,evaluate_monomial]
  simp only [TwistedLocalization.fraction,fraction,LinearMap.coe_mk,AddHom.coe_mk,
    Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [←hd,←map_mul,IsLocalization.mk'_spec,reesAmbient_algebraMap,evaluate_monomial]

lemma reesAmbient_mem (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t) :
    reesAmbient I hw x ∈ piece I w d t := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (reesGrade I) (reesDenominator_mem I hw) t x
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  rw [←ha,hae,reesAmbient_fraction]
  exact fraction_mem I w d t n b

 
def reesMap (t : ℕ) :
    TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t →ₗ[R]
      piece I w d t :=
  ((reesAmbient I hw).toLinearMap.comp
    (TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t).subtype).codRestrict _
      (reesAmbient_mem I hw t)

lemma reesMap_surjective (t : ℕ) : Function.Surjective (reesMap I hw t) := by
  intro x
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  refine ⟨⟨TwistedLocalization.fraction (reesGrade I) (f := reesDenominator I hw) t n
    ⟨monomial I _ a,⟨a,rfl⟩⟩,TwistedLocalization.fraction_mem _ _ _ _⟩,?_⟩
  apply Subtype.ext
  exact (reesAmbient_fraction I hw t n a).trans ha

lemma fraction_zero_iff (t n : ℕ) (a : ↥(I^(n*d+t))) :
    fraction I w d t n a=0 ↔ ∃ k : ℕ, w^k*(a:R)=0 := by
  change Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)=0 ↔ _
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_,k,rfl⟩,hk⟩
    exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨w^k,k,rfl⟩,hk⟩

lemma reesMap_injective (t : ℕ) : Function.Injective (reesMap I hw t) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (reesGrade I) (reesDenominator_mem I hw) t x
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  have he : fraction I w d t n b=0 := by
    have hh := congrArg Subtype.val hx
    change reesAmbient I hw x.val=0 at hh
    rw [←ha,hae,reesAmbient_fraction] at hh
    exact hh
  obtain ⟨k,hk⟩ := (fraction_zero_iff I (w := w) (d := d) t n b).mp he
  apply Subtype.ext
  rw [←ha,hae]
  change Localization.mk (monomial I _ b) (⟨(reesDenominator I hw)^n,n,rfl⟩ : Submonoid.powers _)=0
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨(reesDenominator I hw)^k,k,rfl⟩,?_⟩
  apply Subtype.ext
  change (Polynomial.monomial d w)^k * Polynomial.monomial (n*d+t) (b:R)=0
  rw [Polynomial.monomial_pow,Polynomial.monomial_mul_monomial,hk,Polynomial.monomial_zero_right]


def reesEquiv (t : ℕ) :
    TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t ≃ₗ[R]
      piece I w d t :=
  LinearEquiv.ofBijective (reesMap I hw t) ⟨reesMap_injective I hw t,reesMap_surjective I hw t⟩
end


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w : R} {d : ℕ} (hw : w ∈ I^d)

 
def quotientGraded : reesGrade I →+*ᵍ SourceGraded.targetGrade I where
  toRingHom := Ideal.Quotient.mk (shifted I)
  map_mem hx := ⟨_,hx,rfl⟩

lemma quotientGraded_apply (a : reesAlgebra I) :
    quotientGraded I a=Ideal.Quotient.mk (shifted I) a := rfl

lemma quotientGraded_smul (r : R) (a : reesAlgebra I) :
    quotientGraded I (r • a)=r • quotientGraded I a :=
  (quotientR I).map_smul r a

lemma quotientGraded_surjective : Function.Surjective (quotientGraded I) :=
  Ideal.Quotient.mk_surjective

abbrev exceptionalPiece (t : ℕ) :=
  TwistedLocalization.piece (R := R) (SourceGraded.targetGrade I)
    (f := quotientGraded I (reesDenominator I hw)) (d := d) t

attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap quotientGraded
attribute [local instance] TwistedLocalization.kernelAdd TwistedLocalization.kernelModule
 
def quotientTwist (t : ℕ) :=
  TwistedLocalization.pieceMap (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (reesGrade I) (reesDenominator_mem I hw) (SourceGraded.targetGrade I) (quotientGraded I)
    (quotientGraded_smul I) t

lemma quotientTwist_surjective (t : ℕ) : Function.Surjective (quotientTwist I hw t) := by
  unfold quotientTwist
  apply TwistedLocalization.pieceMap_surjective
  exact quotientGraded_surjective I

lemma quotientTwist_kernel_fraction (t : ℕ)
    (x : TwistedLocalization.piece (reesGrade I) (f := reesDenominator I hw) (d := d) t)
    (hx : quotientTwist I hw t x=0) :
    ∃ (n : ℕ) (a : reesGrade I (n*d+t)), quotientGraded I (a:reesAlgebra I)=0 ∧
      TwistedLocalization.pieceFraction (reesGrade I) (f := reesDenominator I hw) t n a=x := by
  unfold quotientTwist at hx
  exact TwistedLocalization.kernel_fraction_eq (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I)
    (f := reesDenominator I hw) (d := d) (reesGrade I) (reesDenominator_mem I hw)
    (SourceGraded.targetGrade I) (quotientGraded I) (quotientGraded_smul I) t x hx

 
def layerMap (t : ℕ) :=
  (quotientTwist I hw t).comp (reesEquiv I hw t).symm.toLinearMap

lemma layerMap_surjective (t : ℕ) : Function.Surjective (layerMap I hw t) :=
  (quotientTwist_surjective I hw t).comp (reesEquiv I hw t).symm.surjective

lemma layerMap_kernel_le (t : ℕ) : (layerMap I hw t).ker ≤
    (piece I w d (t+1)).comap (piece I w d t).subtype := by
  intro x hx
  have hk : (reesEquiv I hw t).symm x ∈ (quotientTwist I hw t).ker := hx
  obtain ⟨n,a,hga,ha⟩ := quotientTwist_kernel_fraction I hw t ((reesEquiv I hw t).symm x) hk
  obtain ⟨b,hb⟩ := a.property
  have hae : a = ⟨monomial I _ b,⟨b,rfl⟩⟩ := Subtype.ext hb.symm
  have hbk : (b:R) ∈ I^(n*d+t+1) := by
    apply (monomial_mem_shifted_iff I (n*d+t) b).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [hae] at hga
    simpa only [quotientGraded_apply] using hga
  have he : fraction I w d t n b=x.val := by
    have hh := congrArg (reesEquiv I hw t) ha
    rw [LinearEquiv.apply_symm_apply] at hh
    have hh' := congrArg Subtype.val hh
    change reesAmbient I hw (TwistedLocalization.fraction (reesGrade I) t n a)=x.val at hh'
    rw [hae,reesAmbient_fraction] at hh'
    exact hh'
  change x.val ∈ piece I w d (t+1)
  rw [←he]
  exact fraction_mem I w d (t+1) n ⟨b.val,by simpa only [Nat.add_assoc] using hbk⟩

lemma layerMap_kernel_ge (t : ℕ) :
    (piece I w d (t+1)).comap (piece I w d t).subtype ≤ (layerMap I hw t).ker := by
  intro x hx
  obtain ⟨n,b,hb⟩ := exists_fraction I w d hw (t+1) ⟨x.val,hx⟩
  let a : ↥(I^(n*d+t)) := ⟨b.val,Ideal.pow_le_pow_right (by omega) b.property⟩
  let y := TwistedLocalization.pieceFraction (reesGrade I)
    (f := reesDenominator I hw) t n ⟨monomial I _ a,⟨a,rfl⟩⟩
  have he : reesEquiv I hw t y=x := by
    apply Subtype.ext
    exact (reesAmbient_fraction I hw t n a).trans hb
  have hz : quotientGraded I (monomial I _ a)=0 := by
    unfold quotientGraded
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (monomial_mem_shifted_iff I (n*d+t) a).mpr
    simpa only [Nat.add_assoc] using b.property
  have hgz : TwistedLocalization.gradedMap (R := R) (A := reesAlgebra I) (B := IdealGraded.Ring I) (reesGrade I) (SourceGraded.targetGrade I)
      (quotientGraded I) (quotientGraded_smul I) (n*d+t) ⟨monomial I _ a,⟨a,rfl⟩⟩=0 :=
    by
      apply Subtype.ext
      simpa only [TwistedLocalization.gradedMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_zero] using hz
  change layerMap I hw t x=0
  rw [←he]
  change quotientTwist I hw t ((reesEquiv I hw t).symm (reesEquiv I hw t y))=0
  rw [LinearEquiv.symm_apply_apply]
  change TwistedLocalization.pieceMap _ _ _ _ _ t y=0
  rw [TwistedLocalization.pieceMap_fraction,hgz]
  exact (TwistedLocalization.pieceFraction (R := R) (A := IdealGraded.Ring I)
    (SourceGraded.targetGrade I) (f := quotientGraded I (reesDenominator I hw)) t n).map_zero

lemma layerMap_kernel (t : ℕ) : (layerMap I hw t).ker =
    (piece I w d (t+1)).comap (piece I w d t).subtype :=
  le_antisymm (layerMap_kernel_le I hw t) (layerMap_kernel_ge I hw t)


def layerEquiv (t : ℕ) : layer I w d t ≃ₗ[R] exceptionalPiece I hw t :=
  (Submodule.quotEquivOfEq _ _ (layerMap_kernel I hw t).symm).trans
    ((layerMap I hw t).quotKerEquivOfSurjective (layerMap_surjective I hw t))
end Lech.FilteredFraction


namespace Lech.LocalizationCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {h : ℕ} (y : Fin h → A)
  (F G : (s : Finset (Fin h)) → Submodule R (ambient y s))
  (hF : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : F s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ F v)
  (hG : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : G s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ G v)
  (hFG : ∀ s, F s ≤ G s)

 
def inclusionLinear (n : ℕ) : cochains y F n →ₗ[R] cochains y G n where
  toFun x a := ⟨(x a).val,hFG _ (x a).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma inclusionLinear_injective (n : ℕ) : Function.Injective (inclusionLinear y F G hFG n) := by
  intro x x' hx
  funext a
  apply Subtype.ext
  exact congrArg (fun b : G (ActualCech.intersection a) => b.val) (congrFun hx a)

lemma inclusionLinear_d (n : ℕ) (x : cochains y F n) :
    inclusionLinear y F G hFG (n+1) (d y F hF n x)=
      d y G hG n (inclusionLinear y F G hFG n x) := by
  funext a
  apply Subtype.ext
  change ((∑ i : Fin (n+1),(-1:R)^i.val •
    restrict y F hF (ActualCech.intersection_delete a i) (x (a ∘ i.succAbove))).val) =
    ((∑ i : Fin (n+1),(-1:R)^i.val •
    restrict y G hG (ActualCech.intersection_delete a i)
      (inclusionLinear y F G hFG n x (a ∘ i.succAbove))).val)
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  rfl

 
def inclusion : complex y F hF ⟶ complex y G hG :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (inclusionLinear y F G hFG n)) (fun n => by
    change (ModuleCat.ofHom (inclusionLinear y F G hFG n)) ≫
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains y G n))
        (fun n => ModuleCat.ofHom (d y G hG n)) n (n+1)) =
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains y F n))
        (fun n => ModuleCat.ofHom (d y F hF n)) n (n+1)) ≫
        ModuleCat.ofHom (inclusionLinear y F G hFG (n+1))
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (inclusionLinear_d y F G hF hG hFG n x).symm)
end Lech.LocalizationCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

include hz in
lemma denominator_mem (s : Finset (Fin h)) : GradedChart.denominator z s ∈ I^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GradedChart.denominator]
  | @insert i s hi ih =>
    simp only [GradedChart.denominator,Finset.prod_insert hi,Finset.card_insert_of_notMem hi]
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hz i) ih

 
abbrev term (t : ℕ) (s : Finset (Fin h)) :
    Submodule R (LocalizationCech.ambient z s) :=
  FilteredFraction.piece I (GradedChart.denominator z s) s.card t

include hz in
lemma restriction_mem (t : ℕ) {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : term I z t s) :
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd z hsv) x ∈ term I z t v :=
  FilteredFraction.restriction_mem I (denominator_mem I z hz s)
    (denominator_mem I z hz (v\s)) (GradedChart.denominator_mul_sdiff z hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x

 
def complex (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  LocalizationCech.complex z (term I z t) (restriction_mem I z hz t)

 
def inclusion {s t : ℕ} (hst : s ≤ t) : complex I z hz t ⟶ complex I z hz s :=
  LocalizationCech.inclusion z (term I z t) (term I z s)
    (restriction_mem I z hz t) (restriction_mem I z hz s)
    (fun _ => FilteredFraction.antitone I _ _ hst)
end Lech.FilteredCech


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

include hz in
lemma coordinate_mem (i : Fin h) : z i ∈ I := by
  rw [←hz]
  exact Ideal.subset_span (Set.mem_range_self i)

lemma mapR_X (i : Fin h) : mapR I z hz (MvPolynomial.X i)=generator I z hz i := by
  change MvPolynomial.aeval (generator I z hz) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ _


lemma image_denominator_rees (s : Finset (Fin h)) :
    mapR I z hz (GradedChart.denominator MvPolynomial.X s) =
      FilteredFraction.quotientGraded I (FilteredFraction.reesDenominator I
        (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)) := by
  classical
  unfold GradedChart.denominator
  rw [map_prod]
  simp only [mapR_X]
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty,Finset.card_empty]
      change 1=Ideal.Quotient.mk (shifted I) (monomial I 0 ⟨1,_⟩)
      rw [show monomial I 0 ⟨1,by simp⟩=(1:reesAlgebra I) by
        apply Subtype.ext; change Polynomial.monomial 0 (1:R)=1; simp]
      exact (map_one _).symm
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi,ih]
      change Ideal.Quotient.mk (shifted I) (monomial I 1 ⟨z i,_⟩) *
        Ideal.Quotient.mk (shifted I) (monomial I s.card ⟨∏ j ∈ s,z j,_⟩) =
        Ideal.Quotient.mk (shifted I) (monomial I (insert i s).card ⟨∏ j ∈ insert i s,z j,_⟩)
      rw [←map_mul]
      congr 1
      apply Subtype.ext
      change Polynomial.monomial 1 (z i) * Polynomial.monomial s.card (∏ j ∈ s,z j)=
        Polynomial.monomial (insert i s).card (∏ j ∈ insert i s,z j)
      rw [Polynomial.monomial_mul_monomial,Finset.card_insert_of_notMem hi,Finset.prod_insert hi,Nat.add_comm 1]

attribute [local irreducible] TwistedLocalization.piece FilteredFraction.quotientGraded


def exceptionalTermEquiv (s : Finset (Fin h)) (t : ℕ) :
    FilteredFraction.exceptionalPiece I
      (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t ≃ₗ[R]
    ImageCech.term (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
      MvPolynomial.X s t :=
  TwistedLocalization.pieceCongr (R := R) (A := IdealGraded.Ring I) (targetGrade I)
    (f := FilteredFraction.quotientGraded I (FilteredFraction.reesDenominator I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s)))
    (q := mapR I z hz (GradedChart.denominator MvPolynomial.X s)) (d := s.card) (e := s.card)
    (image_denominator_rees I z hz s).symm rfl t


def filteredReduction (s : Finset (Fin h)) (t : ℕ) :
    FilteredCech.term I z t s →ₗ[R]
      ImageCech.term (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I) (sourceGrade I h) (targetGrade I) (mapR I z hz)
        MvPolynomial.X s t :=
  (exceptionalTermEquiv I z hz s t).toLinearMap.comp
    (FilteredFraction.layerMap I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t)

lemma filteredReduction_surjective (s : Finset (Fin h)) (t : ℕ) :
    Function.Surjective (filteredReduction I z hz s t) :=
  (exceptionalTermEquiv I z hz s t).surjective.comp
    (FilteredFraction.layerMap_surjective I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t)

lemma filteredReduction_kernel (s : Finset (Fin h)) (t : ℕ) :
    (filteredReduction I z hz s t).ker =
      (FilteredCech.term I z (t+1) s).comap (FilteredCech.term I z t s).subtype := by
  rw [filteredReduction,LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot.mpr (exceptionalTermEquiv I z hz s t).injective)]
  exact FilteredFraction.layerMap_kernel I (FilteredCech.denominator_mem I z (coordinate_mem I z hz) s) t
end Lech.SourceGraded


namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a)=r • g a)
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

 
def imagePieceTo (t : ℕ) : piece H (f := g f) (d := d) t →ₗ[R]
    piece H (f := g q) (d := e) t :=
  pieceTo H (map_mem g hf) (map_mem g hc) (by rw [←map_mul,hfc]) hdeg t

lemma pieceMap_pieceTo (t : ℕ) (x : piece G (f := f) (d := d) t) :
    pieceMap G (show q ∈ G e from hfc ▸ hdeg ▸ mul_mem_graded hf hc) H g hg t
      (pieceTo G hf hc hfc hdeg t x) =
    imagePieceTo G H g hf hc hfc hdeg t (pieceMap G hf H g hg t x) := by
  apply Subtype.ext
  exact AlgHom.congr_fun (ambientMap_naturality G H g hg (show f ∣ q from ⟨c,hfc.symm⟩)) x.val
end Lech.TwistedLocalization

end

end OAI
