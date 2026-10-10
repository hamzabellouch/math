import Mathlib
import OAI.RingTheory.Multiplicity.TwistedLocalizationPieceMap

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.GradedChart
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)

 
abbrev cochains (n t : ℕ) := (a : Fin n → Fin h) → term G y (ActualCech.intersection a) t

 
def d (n t : ℕ) : cochains G y n t →ₗ[R] cochains G y (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : R)^i.val •
    restrict G y hy (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
end Lech.GradedChart


namespace Lech.PartialLaurent
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev polynomialCochains (h n t : ℕ) :=
  GradedChart.cochains (MvPolynomial.homogeneousSubmodule (Fin h) R)
    (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) n t

def polynomialD (h n t : ℕ) : polynomialCochains R h n t →ₗ[R] polynomialCochains R h (n+1) t :=
  GradedChart.d _ MvPolynomial.X (MvPolynomial.isHomogeneous_X R) n t

def polynomialCochainsEquiv (h n t : ℕ) : polynomialCochains R h n t ≃ₗ[R]
    ActualCech.laurentCochains R h n (t : ℤ) :=
  LinearEquiv.piCongrRight (fun a => polynomialCechEquiv R (ActualCech.intersection a) t)

lemma polynomialCochainsEquiv_d (h n t : ℕ) (f : polynomialCochains R h n t) :
    polynomialCochainsEquiv R h (n+1) t (polynomialD R h n t f) =
      ActualCech.laurentD R h n (t : ℤ) (polynomialCochainsEquiv R h n t f) := by
  funext a
  change polynomialCechEquiv R (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict _ _ _
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,polynomialCechEquiv_naturality]
  rfl

lemma polynomialD_square (h n t : ℕ) (f : polynomialCochains R h n t) :
    polynomialD R h (n+1) t (polynomialD R h n t f)=0 := by
  apply (polynomialCochainsEquiv R h (n+2) t).injective
  rw [polynomialCochainsEquiv_d,polynomialCochainsEquiv_d,ActualCech.laurentD_square,map_zero]


def polynomialComplex (h t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (polynomialCochains R h n t))
    (fun n => ModuleCat.ofHom (polynomialD R h n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact polynomialD_square R h n t f)

lemma polynomial_exact {h : ℕ} (hh : 0<h) (n t : ℕ)
    (f : polynomialCochains R h (n+1) t) (hf : polynomialD R h (n+1) t f=0) :
    ∃ g : polynomialCochains R h n t, polynomialD R h n t g=f := by
  have hl : ActualCech.laurentD R h (n+1) (t : ℤ)
      (polynomialCochainsEquiv R h (n+1) t f)=0 := by
    rw [←polynomialCochainsEquiv_d,hf,map_zero]
  obtain ⟨x,hx⟩ := ActualCech.laurent_exact_nonnegative R hh n (Int.natCast_nonneg t) _ hl
  refine ⟨(polynomialCochainsEquiv R h n t).symm x,?_⟩
  apply (polynomialCochainsEquiv R h (n+1) t).injective
  rw [polynomialCochainsEquiv_d,LinearEquiv.apply_symm_apply,hx]

lemma polynomialComplex_exactAt {h : ℕ} (hh : 0<h) (n t : ℕ) :
    (polynomialComplex R h t).ExactAt (n+1) := by
  apply ((polynomialComplex R h t).exactAt_iff' (i := n) (j := n+1) (k := n+2)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (polynomialCochains R h n t))
    (fun n => ModuleCat.ofHom (polynomialD R h n t)) (n+1) ((n+1)+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  obtain ⟨x,hx⟩ := polynomial_exact R hh n t f hf
  refine ⟨x,?_⟩
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (polynomialCochains R h n t))
    (fun n => ModuleCat.ofHom (polynomialD R h n t)) n (n+1)).hom x=f
  rw [CochainComplex.of_d]
  exact hx
end Lech.PartialLaurent


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grade (h n : ℕ) : Submodule R (MvPolynomial (Fin h) S) :=
  (MvPolynomial.homogeneousSubmodule (Fin h) S n).restrictScalars R

 
def termEquiv (h : ℕ) (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term (grade R S h) MvPolynomial.X s t ≃ₗ[R]
      GradedChart.term (MvPolynomial.homogeneousSubmodule (Fin h) S) MvPolynomial.X s t :=
  (LinearEquiv.ofEq _ _ (TwistedLocalization.piece_restrictScalars (R := R)
    (MvPolynomial.homogeneousSubmodule (Fin h) S) t)).trans
    ((Submodule.restrictScalarsEquiv R S _ _).restrictScalars R)

lemma termEquiv_naturality {h : ℕ} {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : GradedChart.term (grade R S h) MvPolynomial.X s t) :
    termEquiv R S h v t (GradedChart.restrict (grade R S h) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X S) hsv t x) =
    GradedChart.restrict (MvPolynomial.homogeneousSubmodule (Fin h) S) MvPolynomial.X
      (MvPolynomial.isHomogeneous_X S) hsv t (termEquiv R S h s t x) := by
  apply Subtype.ext
  rfl

abbrev cochains (h n t : ℕ) := GradedChart.cochains (grade R S h) MvPolynomial.X n t

def d (h n t : ℕ) : cochains R S h n t →ₗ[R] cochains R S h (n+1) t :=
  GradedChart.d _ MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

def cochainsEquiv (h n t : ℕ) : cochains R S h n t ≃ₗ[R]
    PartialLaurent.polynomialCochains S h n t :=
  LinearEquiv.piCongrRight (fun a => termEquiv R S h (ActualCech.intersection a) t)

lemma cochainsEquiv_d (h n t : ℕ) (f : cochains R S h n t) :
    cochainsEquiv R S h (n+1) t (d R S h n t f) =
      PartialLaurent.polynomialD S h n t (cochainsEquiv R S h n t f) := by
  funext a
  change termEquiv R S h (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict _ _ _
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,termEquiv_naturality]
  change (∑ i : Fin (n+1), (-1 : R)^i.val • _) = ∑ i : Fin (n+1), (-1 : S)^i.val • _
  apply Finset.sum_congr rfl
  intro i _
  rw [← IsScalarTower.algebraMap_smul S, map_pow,map_neg,map_one]
  rfl

lemma d_square (h n t : ℕ) (f : cochains R S h n t) :
    d R S h (n+1) t (d R S h n t f)=0 := by
  apply (cochainsEquiv R S h (n+2) t).injective
  rw [cochainsEquiv_d,cochainsEquiv_d,PartialLaurent.polynomialD_square,map_zero]

def complex (h t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square R S h n t f)

lemma exact {h : ℕ} (hh : 0<h) (n t : ℕ)
    (f : cochains R S h (n+1) t) (hf : d R S h (n+1) t f=0) :
    ∃ g : cochains R S h n t, d R S h n t g=f := by
  have hl : PartialLaurent.polynomialD S h (n+1) t
      (cochainsEquiv R S h (n+1) t f)=0 := by rw [←cochainsEquiv_d,hf,map_zero]
  obtain ⟨x,hx⟩ := PartialLaurent.polynomial_exact S hh n t _ hl
  refine ⟨(cochainsEquiv R S h n t).symm x,?_⟩
  apply (cochainsEquiv R S h (n+1) t).injective
  rw [cochainsEquiv_d,LinearEquiv.apply_symm_apply,hx]

lemma exactAt {h : ℕ} (hh : 0<h) (n t : ℕ) :
    (complex R S h t).ExactAt (n+1) := by
  apply ((complex R S h t).exactAt_iff' (i := n) (j := n+1) (k := n+2)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) (n+1) ((n+1)+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  obtain ⟨x,hx⟩ := exact R S hh n t f hf
  refine ⟨x,?_⟩
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) n (n+1)).hom x=f
  rw [CochainComplex.of_d]
  exact hx
end Lech.RestrictedPolynomialCech


namespace Lech.ImageCech
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)


abbrev term (s : Finset (Fin h)) (t : ℕ) :=
  TwistedLocalization.piece H (f := g (GradedChart.denominator y s)) (d := s.card) t

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma image_denominator (s : Finset (Fin h)) :
    g (GradedChart.denominator y s) = GradedChart.denominator (fun i => g (y i)) s := by
  simp only [GradedChart.denominator,map_prod]

 
def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ) :
    term G H g y s t →ₗ[R] term G H g y v t :=
  TwistedLocalization.pieceTo H (map_mem g (GradedChart.denominator_mem G y hy s))
    (map_mem g (GradedChart.denominator_mem G y hy (v\s)))
    (by rw [←map_mul,GradedChart.denominator_mul_sdiff y hsv])
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t

def mapTerm (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term G y s t →ₗ[R] term G H g y s t :=
  TwistedLocalization.pieceMap G (GradedChart.denominator_mem G y hy s) H g hg t

lemma mapTerm_naturality {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : GradedChart.term G y s t) :
    mapTerm G H g hg y hy v t (GradedChart.restrict G y hy hsv t x) =
      restrict G H g y hy hsv t (mapTerm G H g hg y hy s t x) := by
  apply Subtype.ext
  exact AlgHom.congr_fun (TwistedLocalization.ambientMap_naturality G H g hg
    (GradedChart.denominator_dvd y hsv)) x.val

 
abbrev cochains (n t : ℕ) :=
  (a : Fin n → Fin h) → term G H g y (ActualCech.intersection a) t

def d (n t : ℕ) : cochains G H g y n t →ₗ[R] cochains G H g y (n+1) t where
  toFun f a := ∑ i : Fin (n+1), (-1 : R)^i.val •
    restrict G H g y hy (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))
  map_add' f k := by
    funext a
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    funext a
    simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

def mapCochains (n t : ℕ) : GradedChart.cochains G y n t →ₗ[R] cochains G H g y n t :=
  LinearMap.pi (fun a => (mapTerm G H g hg y hy (ActualCech.intersection a) t).comp
    (LinearMap.proj a))

lemma mapCochains_naturality (n t : ℕ) (f : GradedChart.cochains G y n t) :
    mapCochains G H g hg y hy (n+1) t (GradedChart.d G y hy n t f) =
      d G H g y hy n t (mapCochains G H g hg y hy n t f) := by
  funext a
  change mapTerm G H g hg y hy (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1 : R)^i.val • GradedChart.restrict G y hy
      (ActualCech.intersection_delete a i) t (f (a ∘ i.succAbove))) = _
  simp only [map_sum,map_smul,mapTerm_naturality]
  rfl

include hy in
lemma mapTerm_surjective (hsurj : Function.Surjective g) (s : Finset (Fin h)) (t : ℕ) :
    Function.Surjective (mapTerm G H g hg y hy s t) :=
  TwistedLocalization.pieceMap_surjective _ _ _ _ _ hsurj t

include hy in
lemma mapCochains_surjective (hsurj : Function.Surjective g) (n t : ℕ) :
    Function.Surjective (mapCochains G H g hg y hy n t) := by
  intro f
  choose k hk using fun a => mapTerm_surjective G H g hg y hy hsurj
    (ActualCech.intersection a) t (f a)
  exact ⟨k,funext hk⟩
end Lech.ImageCech


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

abbrev cochains (n t : ℕ) := ImageCech.cochains _ H g MvPolynomial.X n t

def d (n t : ℕ) : cochains H g n t →ₗ[R] cochains H g (n+1) t :=
  ImageCech.d _ H g MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

def mapCochains (n t : ℕ) : RestrictedPolynomialCech.cochains R S h n t →ₗ[R] cochains H g n t :=
  ImageCech.mapCochains _ H g hg MvPolynomial.X (MvPolynomial.isHomogeneous_X S) n t

lemma mapCochains_naturality (n t : ℕ) (f : RestrictedPolynomialCech.cochains R S h n t) :
    mapCochains H g hg (n+1) t (RestrictedPolynomialCech.d R S h n t f) =
      d H g n t (mapCochains H g hg n t f) :=
  ImageCech.mapCochains_naturality _ H g hg MvPolynomial.X
    (MvPolynomial.isHomogeneous_X S) n t f

lemma mapCochains_surjective (hsurj : Function.Surjective g) (n t : ℕ) :
    Function.Surjective (mapCochains H g hg n t) :=
  ImageCech.mapCochains_surjective _ H g hg MvPolynomial.X
    (MvPolynomial.isHomogeneous_X S) hsurj n t

include hg in
lemma d_square (hsurj : Function.Surjective g) (n t : ℕ) (f : cochains H g n t) :
    d H g (n+1) t (d H g n t f)=0 := by
  obtain ⟨x,rfl⟩ := mapCochains_surjective H g hg hsurj n t f
  rw [←mapCochains_naturality,←mapCochains_naturality,
    RestrictedPolynomialCech.d_square,map_zero]


def complex (hsurj : Function.Surjective g) (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains H g n t))
    (fun n => ModuleCat.ofHom (d H g n t)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact d_square H g hg hsurj n t f)

 
def comparison (hsurj : Function.Surjective g) (t : ℕ) :
    RestrictedPolynomialCech.complex R S h t ⟶ complex H g hg hsurj t :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (mapCochains H g hg n t)) (fun n => by
    change (ModuleCat.ofHom (mapCochains H g hg n t)) ≫
      (CochainComplex.of.d (fun n => ModuleCat.of R (cochains H g n t))
        (fun n => ModuleCat.ofHom (d H g n t)) n (n+1)) =
      (CochainComplex.of.d (fun n => ModuleCat.of R (RestrictedPolynomialCech.cochains R S h n t))
        (fun n => ModuleCat.ofHom (RestrictedPolynomialCech.d R S h n t)) n (n+1)) ≫
        ModuleCat.ofHom (mapCochains H g hg (n+1) t)
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (mapCochains_naturality H g hg n t f).symm)
end Lech.RestrictedPolynomialImageCech


namespace Lech.ActualCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (A : Type u) [CommRing A]

lemma laurentD_zero_injective {h : ℕ} (hh : 0<h) (t : ℤ) :
    Function.Injective (laurentD A h 0 t) := by
  intro x y hxy
  funext a
  let u : Fin 1 → Fin h := fun _ => ⟨0,hh⟩
  have he := congrFun hxy u
  change (∑ i : Fin 1, (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete u i) t
      (x (u ∘ i.succAbove))) = (∑ i : Fin 1, (-1 : A)^i.val •
    PartialLaurent.coefficientChartRestrict A (intersection_delete u i) t
      (y (u ∘ i.succAbove))) at he
  simp only [Fin.sum_univ_one,Fin.val_zero,pow_zero,one_smul] at he
  have hae : (u ∘ (0 : Fin 1).succAbove) = a := Subsingleton.elim _ _
  subst a
  apply Subtype.ext
  exact PartialLaurent.restrict_injective A (intersection_delete u 0)
    (congrArg Subtype.val he)
end Lech.ActualCech


namespace Lech.PartialLaurent
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
lemma polynomialD_zero_injective {h : ℕ} (hh : 0<h) (t : ℕ) :
    Function.Injective (polynomialD R h 0 t) := by
  intro x y hxy
  apply (polynomialCochainsEquiv R h 0 t).injective
  apply ActualCech.laurentD_zero_injective R hh (t : ℤ)
  rw [←polynomialCochainsEquiv_d,←polynomialCochainsEquiv_d,hxy]
end Lech.PartialLaurent


namespace Lech.RestrictedPolynomialCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.gradedAlgebra
lemma d_zero_injective {h : ℕ} (hh : 0<h) (t : ℕ) :
    Function.Injective (d R S h 0 t) := by
  intro x y hxy
  apply (cochainsEquiv R S h 0 t).injective
  apply PartialLaurent.polynomialD_zero_injective S hh t
  rw [←cochainsEquiv_d,←cochainsEquiv_d,hxy]

lemma exactAt_zero {h : ℕ} (hh : 0<h) (t : ℕ) :
    (complex R S h t).ExactAt 0 := by
  apply ((complex R S h t).exactAt_iff' (i := 0) (j := 0) (k := 1)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change (CochainComplex.of.d
    (fun n => ModuleCat.of R (cochains R S h n t))
    (fun n => ModuleCat.ofHom (d R S h n t)) 0 (0+1)).hom f=0 at hf
  rw [CochainComplex.of_d] at hf
  have hfz : f=0 := d_zero_injective R S hh t (hf.trans (map_zero _).symm)
  refine ⟨0,?_⟩
  simpa only [map_zero] using hfz.symm

lemma exactAt_all {h : ℕ} (hh : 0<h) (n t : ℕ) :
    (complex R S h t).ExactAt n := by
  cases n with
  | zero => exact exactAt_zero R S hh t
  | succ n => exact exactAt R S hh n t
end Lech.RestrictedPolynomialCech


namespace Lech.RestrictedPolynomialImageCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {h : ℕ} (H : ℕ → Submodule R B) [GradedAlgebra H]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (g : (RestrictedPolynomialCech.grade R S h) →+*ᵍ H)
  (hg : ∀ (r : R) (a : MvPolynomial (Fin h) S), g (r • a) = r • g a)

lemma comparison_f (hsurj : Function.Surjective g) (t n : ℕ) :
    (comparison H g hg hsurj t).f n = ModuleCat.ofHom (mapCochains H g hg n t) := rfl

lemma comparison_termwise (hsurj : Function.Surjective g)
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass] (t : ℕ)
    (hk : ∀ s : Finset (Fin h), P (ModuleCat.of R
      (ImageCech.mapTerm (RestrictedPolynomialCech.grade R S h) H g hg
        MvPolynomial.X (MvPolynomial.isHomogeneous_X S) s t).ker)) (n : ℕ) :
    P.isoModSerre ((comparison H g hg hsurj t).f n) := by
  rw [comparison_f]
  apply piLinear_isoModSerre
  intro a
  apply isoModSerre_of_surjective_kernel
  · exact ImageCech.mapTerm_surjective _ _ _ _ _ _ hsurj _ _
  · exact hk _
end Lech.RestrictedPolynomialImageCech

end

end OAI
