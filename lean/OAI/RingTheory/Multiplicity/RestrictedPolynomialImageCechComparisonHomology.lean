import Mathlib
import OAI.RingTheory.Multiplicity.GradedChartCochains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)
  (hsurj : Function.Surjective g) (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
  (t : ℕ)
  (hk : ∀ s : Finset (Fin h), P (ModuleCat.of R
      (ImageCech.mapTerm (RestrictedPolynomialCech.grade R S h) H g hg
        MvPolynomial.X (MvPolynomial.isHomogeneous_X S) s t).ker))

include hk in
lemma comparison_homology (n : ℕ) :
    P.isoModSerre (homologyMap (comparison H g hg hsurj t) n) :=
  homology_isoModSerre_of_termwise P _
    (comparison_termwise H g hg hsurj P t hk) n

include hk in
lemma homology_mem (hh : 0<h) (n : ℕ) : P ((complex H g hg hsurj t).homology n) :=
  homology_zeroClass_of_termwise_exactAt P _
    (comparison_termwise H g hg hsurj P t hk) n
    (RestrictedPolynomialCech.exactAt_all R S hh n t)
end Lech.RestrictedPolynomialImageCech


namespace Lech.TwistedLocalization
open CategoryTheory CategoryTheory.Limits
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B]
  (G : ℕ → Submodule C A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)
  (H : ℕ → Submodule C B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : C) (a : A), g (r • a) = r • g a)
  (ell : AllModuleLength C)
attribute [local instance] kernelAdd kernelModule
attribute [local irreducible] pieceMap gradedMap kernelFraction
include hf in
omit [GradedAlgebra H] in
lemma kernel_length_zero
    (hker : ∀ n, ell.value (ModuleCat.of C (gradedMap G H g hg n).ker)=0) (t : ℕ) :
    ell.value (ModuleCat.of C (pieceMap G hf H g hg t).ker)=0 := by
  let P := (ell.torsionLength ⊥).zeroClass
  have hz : P (ModuleCat.of C (pieceMap G hf H g hg t).ker) := by
    apply kernel_property G hf H g hg t P
    · intro n
      exact ⟨⟨1,by simp⟩, hker n⟩
    · intro U hU
      refine ⟨⟨1,by simp⟩, ?_⟩
      have hz := ell.iSup_zero (fun n : ULift.{u} ℕ => U n.down)
        (fun n => (hU n.down).2)
      have he : (⨆ n : ULift.{u} ℕ, U n.down) = ⨆ n : ℕ, U n := by
        simp only [iSup_ulift]
      rw [he] at hz
      exact hz
  exact hz.2
end Lech.TwistedLocalization


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
  (ell : AllModuleLength R)
  {f : MvPolynomial (Fin h) (R ⧸ I)} {d : ℕ} (hf : f ∈ sourceGrade I h d)

attribute [local irreducible] TwistedLocalization.piece IdealGraded.polynomialMap
 

def twistMapR (t : ℕ) :=
  TwistedLocalization.pieceMap (R := R) (A := MvPolynomial (Fin h) (R ⧸ I))
    (B := IdealGraded.Ring I) (sourceGrade I h) hf (targetGrade I)
    (mapR I z hz) (mapR_smul I z hz) t

include hz in
 

lemma twist_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t : ℕ) :
    ell.value (ModuleCat.of R (twistMapR I z hz hf t).ker)=0 := by
  unfold twistMapR
  apply TwistedLocalization.kernel_length_zero _ hf _ _ _ ell
  intro n
  exact mapR_degree_kernel_zero I z hz ell hh hmu ha n

include hz in
lemma twist_surjective (t : ℕ) : Function.Surjective (twistMapR I z hz hf t) := by
  apply TwistedLocalization.pieceMap_surjective
  exact mapR_surjective I z hz
end Lech.SourceGraded


namespace Lech.AllModuleLength
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (ell : Lech.AllModuleLength R)
lemma mem_zeroClass (M : ModuleCat.{u} R) (hM : ell.value M=0) :
    (ell.torsionLength ⊥).zeroClass M :=
  ⟨⟨1,by rw [pow_one]; exact bot_le⟩,hM⟩
end Lech.AllModuleLength


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)
  (ell : AllModuleLength R)
attribute [local instance] MvPolynomial.gradedAlgebra


def exceptionalCech (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  RestrictedPolynomialImageCech.complex (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h) (targetGrade I) (mapR I z hz)
    (mapR_smul I z hz) (mapR_surjective I z hz) t

 
def exceptionalComparison (t : ℕ) :=
  RestrictedPolynomialImageCech.comparison (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h) (targetGrade I) (mapR I z hz)
    (mapR_smul I z hz) (mapR_surjective I z hz) t

attribute [local irreducible] TwistedLocalization.piece TwistedLocalization.pieceMap TwistedLocalization.gradedMap ImageCech.mapTerm IdealGraded.polynomialMap

lemma exceptionalMapTerm_kernel_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t : ℕ) (s : Finset (Fin h)) :
    ell.value (ModuleCat.of R (ImageCech.mapTerm (R := R) (A := MvPolynomial (Fin h) (R ⧸ I)) (B := IdealGraded.Ring I)
      (RestrictedPolynomialCech.grade R (R ⧸ I) h) (targetGrade I) (mapR I z hz)
      (mapR_smul I z hz) MvPolynomial.X (MvPolynomial.isHomogeneous_X (R ⧸ I)) s t).ker)=0 := by
  unfold ImageCech.mapTerm
  exact twist_kernel_zero I z hz ell
    (GradedChart.denominator_mem (sourceGrade I h) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X (R ⧸ I)) s) hh hmu ha t

theorem exceptionalComparison_termwise
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t n : ℕ) :
    (ell.torsionLength ⊥).zeroClass.isoModSerre ((exceptionalComparison I z hz t).f n) := by
  have comparison := RestrictedPolynomialImageCech.comparison_termwise (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I)
    (targetGrade I) (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz)
    (ell.torsionLength ⊥).zeroClass t
    (by
      intro s
      constructor
      · exact ⟨1, by rw [pow_one]; exact bot_le⟩
      · exact exceptionalMapTerm_kernel_zero I z hz ell hh hmu ha t s) n
  exact comparison


theorem exceptionalComparison_homology
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t n : ℕ) :
    (ell.torsionLength ⊥).zeroClass.isoModSerre
      (homologyMap (exceptionalComparison I z hz t) n) := by
  have comparison := RestrictedPolynomialImageCech.comparison_homology (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I)
    (targetGrade I) (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz)
    (ell.torsionLength ⊥).zeroClass t
    (by
      intro s
      constructor
      · exact ⟨1, by rw [pow_one]; exact bot_le⟩
      · exact exceptionalMapTerm_kernel_zero I z hz ell hh hmu ha t s) n
  exact comparison


lemma exceptionalCech_homology_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t n : ℕ) :
    ell.value ((exceptionalCech I z hz t).homology n)=0 := by
  have hn := RestrictedPolynomialImageCech.homology_mem (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I)
    (targetGrade I) (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz)
    (ell.torsionLength ⊥).zeroClass t
    (by
      intro s
      constructor
      · exact ⟨1, by rw [pow_one]; exact bot_le⟩
      · exact exceptionalMapTerm_kernel_zero I z hz ell hh hmu ha t s) hh n
  have hv := hn.2
  change ell.value ((exceptionalCech I z hz t).homology n)=0 at hv
  exact hv
end Lech.SourceGraded


namespace Lech.LocalizationCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {h : ℕ} (y : Fin h → A)
abbrev ambient (s : Finset (Fin h)) := Localization.Away (GradedChart.denominator y s)
variable (F : (s : Finset (Fin h)) → Submodule R (ambient y s))
  (hF : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : F s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ F v)

 
def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) : F s →ₗ[R] F v :=
  ((TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv)).toLinearMap.comp
    (F s).subtype).codRestrict _ (hF hsv)

lemma restrict_comp {s v w : Finset (Fin h)} (hsv : s ⊆ v) (hvw : v ⊆ w) (x : F s) :
    restrict y F hF hvw (restrict y F hF hsv x) = restrict y F hF (hsv.trans hvw) x := by
  apply Subtype.ext
  exact AlgHom.congr_fun (TwistedLocalization.ambientTo_comp (GradedChart.denominator_dvd y hsv) (GradedChart.denominator_dvd y hvw)) x.val

abbrev cochains (n : ℕ) := (a : Fin n → Fin h) → F (ActualCech.intersection a)

 
def d (n : ℕ) : cochains y F n →ₗ[R] cochains y F (n+1) where
  toFun f a := ∑ i : Fin (n+1), (-1:R)^i.val •
    restrict y F hF (ActualCech.intersection_delete a i) (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

lemma intersection_comp_subset {N n : ℕ} (a : Fin N → Fin h) (b : Fin n → Fin N) :
    ActualCech.intersection (a ∘ b) ⊆ ActualCech.intersection a := by
  classical
  intro i hi
  simp only [ActualCech.intersection,Finset.mem_image,Finset.mem_univ,true_and] at hi ⊢
  obtain ⟨j,rfl⟩ := hi
  exact ⟨b j,rfl⟩

 
def toFixed {N n : ℕ} (a : Fin N → Fin h) (f : cochains y F n) :
    ActualCech.Row (ambient y (ActualCech.intersection a)) (ι := Fin N) n := fun b =>
  TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b)) (f (a ∘ b)).val

lemma toFixed_self {n : ℕ} (a : Fin n → Fin h) (f : cochains y F n) :
    toFixed y F a f id=(f a).val := by
  change TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a id)) (f (a ∘ id)).val = _
  simp only [Function.comp_id]
  rw [TwistedLocalization.ambientTo_self]
  rfl

lemma toFixed_d {N n : ℕ} (a : Fin N → Fin h) (f : cochains y F n) :
    toFixed y F a (d y F hF n f) =
      ActualCech.delta (ambient y (ActualCech.intersection a)) n (toFixed y F a f) := by
  funext b
  change TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b))
    ((∑ i : Fin (n+1), (-1:R)^i.val •
      restrict y F hF (ActualCech.intersection_delete (a ∘ b) i)
        (f ((a ∘ b) ∘ i.succAbove))).val) = _
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  change (∑ i : Fin (n+1), _) = ∑ i : Fin (n+1), _
  apply Finset.sum_congr rfl
  intro i _
  have he := AlgHom.congr_fun (TwistedLocalization.ambientTo_comp (R := R)
    (GradedChart.denominator_dvd y (ActualCech.intersection_delete (a ∘ b) i))
    (GradedChart.denominator_dvd y (intersection_comp_subset a b)))
    (f ((a ∘ b) ∘ i.succAbove)).val
  change (-1:R)^i.val • ((TwistedLocalization.ambientTo (R := R)
    (GradedChart.denominator_dvd y (intersection_comp_subset a b))).comp
    (TwistedLocalization.ambientTo (R := R)
      (GradedChart.denominator_dvd y (ActualCech.intersection_delete (a ∘ b) i))))
      (f ((a ∘ b) ∘ i.succAbove)).val = _
  rw [he]
  simp only [Algebra.smul_def,map_pow,map_neg,map_one]
  rfl


lemma d_square (n : ℕ) (f : cochains y F n) :
    d y F hF (n+1) (d y F hF n f)=0 := by
  funext a
  apply Subtype.ext
  have he : toFixed y F a (d y F hF (n+1) (d y F hF n f))=0 := by
    rw [toFixed_d,toFixed_d,ActualCech.delta_square]
  have ha := congrFun he id
  rw [toFixed_self] at ha
  exact ha

 
def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains y F n))
    (fun n => ModuleCat.ofHom (d y F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square y F hF n f)
end Lech.LocalizationCech


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

lemma monomial_mul (i j : ℕ) (a : ↥(I^i)) (b : ↥(I^j)) :
    monomial I i a * monomial I j b = monomial I (i+j)
      ⟨(a:R)*(b:R),by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ := by
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

instance reesGradedAlgebra : GradedAlgebra (reesGrade I) where
  toDecomposition := reesDecomposition I
  one_mem := by
    refine ⟨⟨1,by simp⟩,?_⟩
    apply Subtype.ext
    simp
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x,rfl⟩ := ha
    obtain ⟨y,rfl⟩ := hb
    exact ⟨⟨(x:R)*(y:R),by rw [pow_add]; exact Ideal.mul_mem_mul x.2 y.2⟩,
      (monomial_mul I i j x y).symm⟩


def evaluate : reesAlgebra I →ₐ[R] R :=
  (Polynomial.aeval (1:R)).comp (reesAlgebra I).val

@[simp] lemma evaluate_monomial (i : ℕ) (a : ↥(I^i)) :
    evaluate I (monomial I i a) = (a:R) := by
  change Polynomial.eval₂ (algebraMap R R) 1 (Polynomial.monomial i (a:R)) = _
  simp

lemma evaluate_injective_on_grade (i : ℕ) :
    Function.Injective (fun a : reesGrade I i => evaluate I a) := by
  rintro ⟨a,x,rfl⟩ ⟨b,y,rfl⟩ h
  apply Subtype.ext
  apply congrArg (monomial I i)
  apply Subtype.ext
  simpa using h
end Lech.IdealGraded


namespace Lech.FilteredFraction

section
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

 
def fraction (t n : ℕ) : ↥(I^(n*d+t)) →ₗ[R] Localization.Away w where
  toFun a := Localization.mk (a : R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)
  map_add' _ _ := (Localization.add_mk_self _ _ _).symm
  map_smul' _ _ := (Localization.smul_mk _ _ _).symm

 
def piece (t : ℕ) : Submodule R (Localization.Away w) :=
  ⨆ n : ℕ, LinearMap.range (fraction I w d t n)

lemma fraction_mem (t n : ℕ) (a : ↥(I^(n*d+t))) :
    fraction I w d t n a ∈ piece I w d t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

variable (hw : w ∈ I^d)
include hw
lemma raise_fraction (t n k : ℕ) (a : ↥(I^(n*d+t))) :
    ∃ b : ↥(I^((k+n)*d+t)), fraction I w d t (k+n) b = fraction I w d t n a := by
  have hp : w^k ∈ I^(k*d) := by
    simpa only [pow_mul,mul_comm k d] using Ideal.pow_mem_pow hw k
  have hb : w^k*(a:R) ∈ I^((k+n)*d+t) := by
    rw [add_mul,add_assoc,pow_add]
    exact Ideal.mul_mem_mul hp a.property
  refine ⟨⟨w^k*(a:R),hb⟩,?_⟩
  dsimp [fraction]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

lemma range_mono (t : ℕ) : Monotone (fun n : ℕ => LinearMap.range (fraction I w d t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction I w d hw t n k a

lemma exists_fraction (t : ℕ) (x : piece I w d t) :
    ∃ (n : ℕ) (a : ↥(I^(n*d+t))), fraction I w d t n a=(x:Localization.Away w) := by
  have hx := x.property
  change x.val ∈ (⨆ n, LinearMap.range (fraction I w d t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono I w d hw t).directed_le] at hx
  exact hx
omit hw

lemma antitone : Antitone (piece I w d) := by
  intro s t hst
  apply iSup_le
  intro n
  rintro _ ⟨a,rfl⟩
  exact fraction_mem I w d s n ⟨a.val,Ideal.pow_le_pow_right (by omega) a.property⟩

 
abbrev layer (t : ℕ) := piece I w d t ⧸ (piece I w d (t+1)).comap (piece I w d t).subtype

 
abbrev thickening (m : ℕ) := piece I w d 0 ⧸ (piece I w d m).comap (piece I w d 0).subtype
end


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hc hdeg in
lemma restriction_fraction (t n : ℕ) (a : ↥(I^(n*d+t))) :
    ∃ b : ↥(I^(n*e+t)),
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
        (fraction I w d t n a) = fraction I v e t n b := by
  have hp : c^n ∈ I^(n*k) := by
    simpa only [pow_mul,mul_comm n k] using Ideal.pow_mem_pow hc n
  have hb : (a:R)*c^n ∈ I^(n*e+t) := by
    have heq : n*d+t+n*k=n*e+t := by rw [←hdeg]; ring
    rw [←heq,pow_add]
    exact Ideal.mul_mem_mul a.property hp
  exact ⟨⟨(a:R)*c^n,hb⟩,TwistedLocalization.ambientTo_mk hwc a n⟩

include hw hc hdeg in
lemma restriction_mem (t : ℕ) (x : piece I w d t) :
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x ∈
      piece I v e t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  obtain ⟨b,hb⟩ := restriction_fraction I hc hwc hdeg t n a
  rw [←ha,hb]
  exact fraction_mem I v e t n b

 
def restrict (t : ℕ) : piece I w d t →ₗ[R] piece I v e t :=
  ((TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)).toLinearMap.comp
    (piece I w d t).subtype).codRestrict _ (restriction_mem I hw hc hwc hdeg t)

@[simp] lemma restrict_val (t : ℕ) (x : piece I w d t) :
    (restrict I hw hc hwc hdeg t x).val =
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x := rfl

 
def inclusion {s t : ℕ} (hst : s ≤ t) : piece I w d t →ₗ[R] piece I w d s :=
  Submodule.inclusion (antitone I w d hst)

lemma restrict_inclusion {s t : ℕ} (hst : s ≤ t) (x : piece I w d t) :
    restrict I hw hc hwc hdeg s (inclusion I hst x) =
      inclusion I hst (restrict I hw hc hwc hdeg t x) := rfl
end Lech.FilteredFraction

end

end OAI
