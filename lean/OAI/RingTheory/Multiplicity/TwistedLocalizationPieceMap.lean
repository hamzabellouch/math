import Mathlib
import OAI.RingTheory.Multiplicity.LechPiIso

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

omit [GradedAlgebra H] in
lemma pieceMap_injective (hinj : Function.Injective g) (t : ℕ) :
    Function.Injective (pieceMap G hf H g hg t) := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  obtain ⟨n,a,ha⟩ := kernel_fraction G hf H g hg t ⟨x,hx⟩
  have haz : (a : G (n*d+t)) = 0 := by
    apply Subtype.ext
    apply hinj
    have hz := congrArg Subtype.val a.property
    simpa only [gradedMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero,
      map_zero] using hz
  simpa only [haz,map_zero,Submodule.mem_bot] using ha.symm

 

def pieceEquiv (hbij : Function.Bijective g) (t : ℕ) :
    piece G (f := f) (d := d) t ≃ₗ[R] piece H (f := g f) (d := d) t :=
  LinearEquiv.ofBijective (pieceMap G hf H g hg t)
    ⟨pieceMap_injective G hf H g hg hbij.1 t,
      pieceMap_surjective G hf H g hg hbij.2 t⟩

omit [GradedAlgebra G] in
 

def pieceCongr {q : A} {e : ℕ} (hq : f=q) (he : d=e) (t : ℕ) :
    piece G (f := f) (d := d) t ≃ₗ[R] piece G (f := q) (d := e) t := by
  subst q; subst e; exact LinearEquiv.refl R _

variable {S D : Type u} [CommRing S] [CommRing D] [Algebra R S]
  [Algebra S D] [Algebra R D] [IsScalarTower R S D]
  (J : ℕ → Submodule S D) {a : D} {k : ℕ}

lemma piece_restrictScalars (t : ℕ) :
    piece (fun n => (J n).restrictScalars R) (f := a) (d := k) t =
      (piece J (f := a) (d := k) t).restrictScalars R := by
  unfold piece
  rw [Submodule.restrictScalars_iSup]
  congr 1

end Lech.TwistedLocalization


namespace Lech.TwistedLocalization
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]

 

lemma pieceCongr_pieceTo {f f' q q' c c' : A} {d d' e e' k k' : ℕ}
    (hf : f ∈ G d) (hc : c ∈ G k) (hfc : f*c=q) (hdeg : d+k=e)
    (hf' : f' ∈ G d') (hc' : c' ∈ G k') (hfc' : f'*c'=q') (hdeg' : d'+k'=e')
    (hff' : f=f') (hqq' : q=q') (hdd' : d=d') (hee' : e=e') (t : ℕ)
    (x : piece G (f := f) (d := d) t) :
    pieceCongr G hqq' hee' t (pieceTo G hf hc hfc hdeg t x) =
      pieceTo G hf' hc' hfc' hdeg' t (pieceCongr G hff' hdd' t x) := by
  subst f'; subst q'; subst d'; subst e'
  apply Subtype.ext
  rfl
end Lech.TwistedLocalization


namespace Lech.GradedChart
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)

 
def denominator (s : Finset (Fin h)) : A := ∏ i ∈ s, y i

include hy in
lemma denominator_mem (s : Finset (Fin h)) : denominator y s ∈ G s.card := by
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,denominator] using
    (prod_mem_graded G (fun _ : Fin h => 1) y (F := s) (fun i _ => hy i))

lemma denominator_mul_sdiff {s v : Finset (Fin h)} (hsv : s ⊆ v) :
    denominator y s * denominator y (v\s) = denominator y v := by
  classical
  unfold denominator
  rw [mul_comm]
  exact Finset.prod_sdiff hsv

lemma denominator_dvd {s v : Finset (Fin h)} (hsv : s ⊆ v) :
    denominator y s ∣ denominator y v := ⟨_,(denominator_mul_sdiff y hsv).symm⟩

abbrev term (s : Finset (Fin h)) (t : ℕ) :=
  TwistedLocalization.piece G (f := denominator y s) (d := s.card) t

 
def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ) :
    term G y s t →ₗ[R] term G y v t :=
  TwistedLocalization.pieceTo G (denominator_mem G y hy s)
    (denominator_mem G y hy (v\s)) (denominator_mul_sdiff y hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t

@[simp] lemma restrict_val {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : term G y s t) : (restrict G y hy hsv t x : Localization.Away (denominator y v)) =
      TwistedLocalization.ambientTo (R := R) (denominator_dvd y hsv) x := rfl

lemma restrict_comp {s v w : Finset (Fin h)} (hsv : s ⊆ v) (hvw : v ⊆ w) (t : ℕ) :
    (restrict G y hy hvw t).comp (restrict G y hy hsv t) =
      restrict G y hy (hsv.trans hvw) t := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change TwistedLocalization.ambientTo (R := R) (denominator_dvd y hvw)
    (TwistedLocalization.ambientTo (R := R) (denominator_dvd y hsv) x) =
      TwistedLocalization.ambientTo (R := R) (denominator_dvd y (hsv.trans hvw)) x
  exact AlgHom.congr_fun (TwistedLocalization.ambientTo_comp
    (denominator_dvd y hsv) (denominator_dvd y hvw)) x

lemma restrict_self (s : Finset (Fin h)) (t : ℕ) :
    restrict G y hy (le_refl s) t = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact AlgHom.congr_fun (TwistedLocalization.ambientTo_self (denominator y s)) x

end Lech.GradedChart


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))

instance laurentScalarTower : IsScalarTower R (Poly R (h := h)) (Laurent R s) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (mapDomainRingHom_comp_algebraMap (R := R) (A := R) (fromNat s)).symm

 

def localizationEquiv : Localization.Away (denominator R s) ≃ₐ[R] Laurent R s :=
  (IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)).restrictScalars R

lemma localizationEquiv_fraction (t n : ℕ) (a : polyGrade R (n*s.card+t)) :
    localizationEquiv R s
      (TwistedLocalization.fraction (polyGrade R) (f := denominator R s) t n a) =
      algebraMap (Poly R (h := h)) (Laurent R s) a * AddMonoidAlgebra.single (n • negativeIndicator s) 1 := by
  change IsLocalization.algEquiv (Submonoid.powers (denominator R s))
    (Localization.Away (denominator R s)) (Laurent R s)
      (Localization.mk (a : Poly R) ⟨(denominator R s)^n,n,rfl⟩) = _
  rw [Localization.mk_eq_mk',IsLocalization.algEquiv_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),inverse_denominator,mul_one]

lemma localizationEquiv_mem (t : ℕ)
    (x : TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t) :
    localizationEquiv R s x ∈ laurentGrade R s (t : ℤ) := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (polyGrade R)
    (denominator_homogeneous R s) t x
  rw [←ha,localizationEquiv_fraction]
  have hm := mul_mem_graded (algebraMap_homogeneous R s a.property)
    (inverse_denominator_homogeneous R s n)
  have hi : ((n*s.card+t : ℕ) : ℤ) + (-(n*s.card : ℕ) : ℤ) = (t : ℤ) := by omega
  simpa only [hi] using hm

 

def twistToLaurent (t : ℕ) :
    TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t →ₗ[R]
      laurentGrade R s (t : ℤ) :=
  ((localizationEquiv R s).toLinearMap.comp
    (TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t).subtype).codRestrict _ (localizationEquiv_mem R s t)

lemma twistToLaurent_surjective (t : ℕ) : Function.Surjective (twistToLaurent R s t) := by
  intro x
  obtain ⟨n,a,ha⟩ := clear_denominators R s x.val
  have hd : (denominator R s)^n ∈ polyGrade R (n*s.card) := by
    simpa only [nsmul_eq_mul,Nat.cast_id] using pow_mem_graded n (denominator_homogeneous R s)
  have hm := mul_mem_graded x.property (algebraMap_homogeneous R s hd)
  rw [ha] at hm
  have hap : a ∈ polyGrade R (n*s.card+t) := (algebraMap_homogeneous_iff R s).mp (by
    have hi : (t : ℤ) + ((n*s.card : ℕ) : ℤ) = ((n*s.card+t : ℕ) : ℤ) := by omega
    simpa only [hi] using hm)
  refine ⟨TwistedLocalization.pieceFraction (polyGrade R)
    (f := denominator R s) t n ⟨a,hap⟩,?_⟩
  apply Subtype.ext
  change localizationEquiv R s (TwistedLocalization.fraction _ t n ⟨a,hap⟩) = x.val
  rw [localizationEquiv_fraction,←ha,mul_assoc,inverse_denominator,mul_one]

def twistLaurentEquiv (t : ℕ) :
    TwistedLocalization.piece (polyGrade R) (f := denominator R s) (d := s.card) t ≃ₗ[R]
      laurentGrade R s (t : ℤ) :=
  LinearEquiv.ofBijective (twistToLaurent R s t)
    ⟨fun _ _ he => Subtype.ext ((localizationEquiv R s).injective
      (congrArg Subtype.val he)),twistToLaurent_surjective R s t⟩

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] {h : ℕ}

lemma polynomialEquiv_grade_iff {p : MvPolynomial (Fin h) R} {n : ℕ} :
    polynomialEquiv R p ∈ polyGrade R n ↔
      p ∈ MvPolynomial.homogeneousSubmodule (Fin h) R n := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,mem_supported]
  change (∀ a : Fin h → ℕ, a ∈ (polynomialEquiv R p).coeff.support →
    totalDegreeNat a = n) ↔ _
  constructor
  · intro hp a ha
    have hs : ((Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)) a) ∈
        (polynomialEquiv R p).coeff.support := by
      rw [Finsupp.mem_support_iff]
      simpa [polynomialEquiv,coeff_domCongr] using Finsupp.mem_support_iff.mp ha
    have hh := hp _ hs
    change a.degree = n
    simpa only [totalDegreeNat,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      Finsupp.degree_eq_sum,Finsupp.linearEquivFunOnFinite_apply] using hh
  · intro hp a ha
    let b := (Finsupp.linearEquivFunOnFinite ℕ ℕ (Fin h)).symm a
    have hb : b ∈ (AddMonoidAlgebra.coeff p).support := by
      rw [Finsupp.mem_support_iff]
      simpa [b,polynomialEquiv,coeff_domCongr] using Finsupp.mem_support_iff.mp ha
    have hh : b.degree = n := hp hb
    change (∑ i,a i) = n
    simpa only [Finsupp.degree_eq_sum,b,Finsupp.linearEquivFunOnFinite_symm_apply,
      Finsupp.linearEquivFunOnFinite_apply] using hh

def polynomialGraded :
    MvPolynomial.homogeneousSubmodule (Fin h) R →+*ᵍ polyGrade R (h := h) where
  toRingHom := (polynomialEquiv R).toRingHom
  map_mem hp := (polynomialEquiv_grade_iff R).mpr hp

end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} (s : Finset (Fin h))
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialDenominator : MvPolynomial (Fin h) R := ∏ i ∈ s, MvPolynomial.X i

lemma polynomialDenominator_homogeneous :
    polynomialDenominator R s ∈ MvPolynomial.homogeneousSubmodule (Fin h) R s.card := by
  rw [←polynomialEquiv_grade_iff,polynomialDenominator,polynomialEquiv_denominator]
  exact denominator_homogeneous R s

instance polynomialLaurentAlgebra : Algebra (MvPolynomial (Fin h) R) (Laurent R s) :=
  ((algebraMap (Poly R (h := h)) (Laurent R s)).comp (polynomialEquiv R).toRingHom).toAlgebra

@[simp] lemma polynomial_algebraMap (a : MvPolynomial (Fin h) R) :
    algebraMap (MvPolynomial (Fin h) R) (Laurent R s) a =
      algebraMap (Poly R (h := h)) (Laurent R s) (polynomialEquiv R a) := rfl

instance polynomialLaurentTower : IsScalarTower R (MvPolynomial (Fin h) R) (Laurent R s) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro r
  change algebraMap R (Laurent R s) r = algebraMap (Poly R) (Laurent R s)
    (polynomialEquiv R (algebraMap R (MvPolynomial (Fin h) R) r))
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply R (Poly R) (Laurent R s) r

 

instance polynomialLocalization : IsLocalization.Away (polynomialDenominator R s) (Laurent R s) := by
  apply IsLocalization.of_ringEquiv_left (polynomialEquiv R).toRingEquiv
    (M₁ := Submonoid.powers (denominator R s))
  · rw [Submonoid.map_powers]
    congr 1
    exact polynomialEquiv_denominator R s
  · intro a
    rfl

def polynomialLocalizationEquiv : Localization.Away (polynomialDenominator R s) ≃ₐ[R] Laurent R s :=
  (IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)).restrictScalars R

lemma polynomialLocalizationEquiv_fraction (t n : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin h) R (n*s.card+t)) :
    polynomialLocalizationEquiv R s
      (TwistedLocalization.fraction (MvPolynomial.homogeneousSubmodule (Fin h) R)
        (f := polynomialDenominator R s) t n a) =
    algebraMap (Poly R (h := h)) (Laurent R s) (polynomialEquiv R a) *
      AddMonoidAlgebra.single (n • negativeIndicator s) 1 := by
  change IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)
      (Localization.mk (a : MvPolynomial (Fin h) R) ⟨(polynomialDenominator R s)^n,n,rfl⟩) = _
  rw [Localization.mk_eq_mk',IsLocalization.algEquiv_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  simp only [polynomial_algebraMap,map_pow,polynomialDenominator,polynomialEquiv_denominator]
  rw [mul_assoc,mul_comm (AddMonoidAlgebra.single _ _),←map_pow,inverse_denominator,mul_one]

lemma polynomialLocalizationEquiv_mem (t : ℕ)
    (x : TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t) :
    polynomialLocalizationEquiv R s x ∈ laurentGrade R s (t : ℤ) := by
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction _
    (polynomialDenominator_homogeneous R s) t x
  rw [←ha,polynomialLocalizationEquiv_fraction]
  have hm := mul_mem_graded (algebraMap_homogeneous R s
    ((polynomialEquiv_grade_iff R).mpr a.property)) (inverse_denominator_homogeneous R s n)
  have hi : ((n*s.card+t : ℕ) : ℤ) + (-(n*s.card : ℕ) : ℤ) = (t : ℤ) := by omega
  simpa only [hi] using hm

def polynomialTwistToLaurent (t : ℕ) :
    TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t →ₗ[R] laurentGrade R s (t : ℤ) :=
  ((polynomialLocalizationEquiv R s).toLinearMap.comp
    (TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t).subtype).codRestrict _
        (polynomialLocalizationEquiv_mem R s t)

lemma polynomialTwistToLaurent_surjective (t : ℕ) :
    Function.Surjective (polynomialTwistToLaurent R s t) := by
  intro x
  obtain ⟨y,hy⟩ := twistToLaurent_surjective R s t x
  obtain ⟨n,a,ha⟩ := TwistedLocalization.exists_fraction (polyGrade R)
    (denominator_homogeneous R s) t y
  have hx : algebraMap (Poly R (h := h)) (Laurent R s) a *
      AddMonoidAlgebra.single (n • negativeIndicator s) 1 = x.val := by
    rw [←localizationEquiv_fraction R s t n a,ha]
    exact congrArg Subtype.val hy
  let p := (polynomialEquiv R).symm (a : Poly R (h := h))
  have hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin h) R (n*s.card+t) := by
    rw [←polynomialEquiv_grade_iff]
    simpa only [p,AlgEquiv.apply_symm_apply] using a.property
  refine ⟨TwistedLocalization.pieceFraction _ (f := polynomialDenominator R s) t n ⟨p,hp⟩,?_⟩
  apply Subtype.ext
  change polynomialLocalizationEquiv R s (TwistedLocalization.fraction _ t n ⟨p,hp⟩) = x.val
  rw [polynomialLocalizationEquiv_fraction]
  simpa only [p,AlgEquiv.apply_symm_apply] using hx

 

def polynomialTwistEquiv (t : ℕ) :
    TwistedLocalization.piece (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (f := polynomialDenominator R s) (d := s.card) t ≃ₗ[R] laurentGrade R s (t : ℤ) :=
  LinearEquiv.ofBijective (polynomialTwistToLaurent R s t)
    ⟨fun _ _ he => Subtype.ext ((polynomialLocalizationEquiv R s).injective
      (congrArg Subtype.val he)),polynomialTwistToLaurent_surjective R s t⟩
end Lech.PartialLaurent


namespace Lech.PartialLaurent
open AddMonoidAlgebra SetLike
universe u
variable (R : Type u) [CommRing R] {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v)
attribute [local instance] MvPolynomial.gradedAlgebra

 
def restrictAlgHom : Laurent R s →ₐ[R] Laurent R v :=
  { restrict R hsv with
    commutes' := fun r => by
      change restrict R hsv (algebraMap R (Laurent R s) r) = algebraMap R (Laurent R v) r
      rw [IsScalarTower.algebraMap_apply R (Poly R (h := h)) (Laurent R s),
        restrict_algebraMap, ←IsScalarTower.algebraMap_apply R (Poly R (h := h)) (Laurent R v)] }

@[simp] lemma polynomialLocalizationEquiv_algebraMap (a : MvPolynomial (Fin h) R) :
    polynomialLocalizationEquiv R s (algebraMap _ _ a) =
      algebraMap _ (Laurent R s) a := by
  exact (IsLocalization.algEquiv (Submonoid.powers (polynomialDenominator R s))
    (Localization.Away (polynomialDenominator R s)) (Laurent R s)).commutes a

 

lemma polynomialLocalizationEquiv_naturality :
    (restrictAlgHom R hsv).comp (polynomialLocalizationEquiv R s).toAlgHom =
    (polynomialLocalizationEquiv R v).toAlgHom.comp
      (TwistedLocalization.ambientTo (R := R)
        (GradedChart.denominator_dvd (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) hsv)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (polynomialDenominator R s))
  apply AlgHom.ext
  intro a
  change restrict R hsv (polynomialLocalizationEquiv R s (algebraMap _ _ a)) =
    polynomialLocalizationEquiv R v (TwistedLocalization.ambientTo (R := R)
      (GradedChart.denominator_dvd (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) hsv)
      (algebraMap _ _ a))
  rw [polynomialLocalizationEquiv_algebraMap,TwistedLocalization.ambientTo_algebraMap]
  change restrict R hsv (algebraMap (MvPolynomial (Fin h) R) (Laurent R s) a) =
    polynomialLocalizationEquiv R v
      (algebraMap (MvPolynomial (Fin h) R) (Localization.Away (polynomialDenominator R v)) a)
  rw [polynomialLocalizationEquiv_algebraMap,polynomial_algebraMap,restrict_algebraMap,
    polynomial_algebraMap]

lemma polynomialTwistEquiv_naturality (t : ℕ)
    (x : GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) s t) :
    polynomialTwistEquiv R v t
      (GradedChart.restrict (MvPolynomial.homogeneousSubmodule (Fin h) R)
        MvPolynomial.X (fun i => MvPolynomial.isHomogeneous_X R i) hsv t x) =
    homogeneousRestrict R hsv (t : ℤ) (polynomialTwistEquiv R s t x) := by
  apply Subtype.ext
  exact (AlgHom.congr_fun (polynomialLocalizationEquiv_naturality R hsv) x.val).symm

 

def polynomialCechEquiv (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) s t ≃ₗ[R]
      homogeneous R s (t : ℤ) :=
  (polynomialTwistEquiv R s t).trans
    (LinearEquiv.ofEq _ _ (homogeneous_eq_grade R s (t : ℤ)).symm)

lemma polynomialCechEquiv_naturality (t : ℕ)
    (x : GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) s t) :
    polynomialCechEquiv R v t
      (GradedChart.restrict (MvPolynomial.homogeneousSubmodule (Fin h) R)
        MvPolynomial.X (fun i => MvPolynomial.isHomogeneous_X R i) hsv t x) =
    coefficientChartRestrict R hsv (t : ℤ) (polynomialCechEquiv R s t x) := by
  apply Subtype.ext
  exact (AlgHom.congr_fun (polynomialLocalizationEquiv_naturality R hsv) x.val).symm
end Lech.PartialLaurent
end

end OAI
