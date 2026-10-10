import Mathlib
import OAI.RingTheory.Multiplicity.LechBoundedEquiv

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev Ring := reesAlgebra I ⧸ shifted I

lemma scalar_mem_shifted {r : R} (hr : r ∈ I) :
    algebraMap R (reesAlgebra I) r ∈ shifted I := by
  intro i
  change (Polynomial.C r).coeff i ∈ I ^ (i + 1)
  by_cases hi : i = 0
  · subst i; simpa using hr
  · simp [Polynomial.coeff_C, hi]

noncomputable instance gradedAlgebra : Algebra (R ⧸ I) (Ring I) :=
  Ideal.Quotient.algebraQuotientOfLEComap (fun _ hr => scalar_mem_shifted I hr)

instance gradedTower : IsScalarTower R (R ⧸ I) (Ring I) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

abbrev quotientR : reesAlgebra I →ₗ[R] Ring I := (shifted I).mkQ.restrictScalars R

lemma quotientR_ker_homogeneous : (quotientR I).ker.IsHomogeneous (reesGrade I) := by
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  exact shifted_homogeneous I

noncomputable instance imageGrading : Decomposition (Grading.imagePiece (reesGrade I) (quotientR I)) :=
  Grading.imageDecomposition (reesGrade I) (quotientR I)
    (shifted I).mkQ_surjective (quotientR_ker_homogeneous I)

def grade (i : ℕ) : Submodule (R ⧸ I) (Ring I) where
  toAddSubmonoid := (Grading.imagePiece (reesGrade I) (quotientR I) i).toAddSubmonoid
  smul_mem' a x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change r • x ∈ _
    exact (Grading.imagePiece (reesGrade I) (quotientR I) i).smul_mem r hx

noncomputable instance gradeDecomposition : Decomposition (grade I) where
  decompose' := decompose (Grading.imagePiece (reesGrade I) (quotientR I))
  left_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).left_inv
  right_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).right_inv

lemma monomial_mem_shifted_iff (i : ℕ) (x : ↥(I ^ i)) :
    monomial I i x ∈ shifted I ↔ (x : R) ∈ I ^ (i + 1) := by
  constructor
  · intro hx
    have h := hx i
    simpa using h
  · intro hx j
    change (Polynomial.monomial i (x : R)).coeff j ∈ I ^ (j + 1)
    by_cases hij : i = j
    · subst j; simpa using hx
    · simp [Polynomial.coeff_monomial, hij]

def toRingR (i : ℕ) : Piece I i →ₗ[R] Ring I :=
  (nextPower I i).liftQ ((quotientR I).comp (monomial I i)) (by
    intro x hx
    change Ideal.Quotient.mk (shifted I) (monomial I i x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((monomial_mem_shifted_iff I i x).mpr hx))

lemma toRingR_injective (i : ℕ) : Function.Injective (toRingR I i) := by
  rw [← LinearMap.ker_eq_bot, toRingR, Submodule.ker_liftQ_eq_bot]
  intro x hx
  change (x : R) ∈ I ^ (i + 1)
  apply (monomial_mem_shifted_iff I i x).mp
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

lemma toRingR_mem (i : ℕ) (x : Piece I i) : toRingR I i x ∈ grade I i := by
  obtain ⟨x, rfl⟩ := (nextPower I i).mkQ_surjective x
  exact ⟨monomial I i x, ⟨x, rfl⟩, rfl⟩

def toPiece (i : ℕ) : Piece I i →ₗ[R ⧸ I] grade I i where
  toFun x := ⟨toRingR I i x, toRingR_mem I i x⟩
  map_add' x y := Subtype.ext ((toRingR I i).map_add x y)
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Subtype.ext
    change toRingR I i (r • x) = r • toRingR I i x
    exact (toRingR I i).map_smul r x

lemma toPiece_bijective (i : ℕ) : Function.Bijective (toPiece I i) := by
  constructor
  · intro x y h
    apply toRingR_injective I i
    exact congrArg Subtype.val h
  · rintro ⟨_, p, ⟨x, rfl⟩, rfl⟩
    exact ⟨(nextPower I i).mkQ x, rfl⟩

noncomputable def pieceEquiv (i : ℕ) : Piece I i ≃ₗ[R ⧸ I] grade I i :=
  LinearEquiv.ofBijective (toPiece I i) (toPiece_bijective I i)

instance gradeFinite [IsNoetherianRing R] (i : ℕ) : Module.Finite (R ⧸ I) (grade I i) :=
  Module.Finite.of_surjective (toPiece I i) (toPiece_bijective I i).2

lemma grade_mul {i j : ℕ} {x y : Ring I} (hx : x ∈ grade I i) (hy : y ∈ grade I j) :
    x * y ∈ grade I (i + j) := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
  let c : ↥(I ^ (i + j)) := ⟨(a : R) * (b : R), by
    rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩
  refine ⟨monomial I (i + j) c, ⟨c, rfl⟩, ?_⟩
  change Ideal.Quotient.mk (shifted I) (monomial I (i + j) c) =
    Ideal.Quotient.mk (shifted I) (monomial I i a) *
      Ideal.Quotient.mk (shifted I) (monomial I j b)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact (Polynomial.monomial_mul_monomial _ _ _ _).symm

lemma exists_generators [IsNoetherianRing R] :
    ∃ (n : ℕ) (x : Fin n → Ring I),
      Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ ∧ ∀ j, x j ∈ grade I 1 := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  have hamem (j : Fin n) : a j ∈ I ^ 1 := by
    rw [pow_one, ← ha]
    exact Submodule.subset_span (Set.mem_range_self j)
  let u : Fin n → reesAlgebra I := fun j => monomial I 1 ⟨a j, hamem j⟩
  have hupoly : Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) =
      reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← ha, Submodule.map_span, Algebra.adjoin_span,
      ← Set.range_comp]
    rfl
  have hu : Algebra.adjoin R (Set.range u) = ⊤ := by
    apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    change Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) = _
    rw [hupoly]
    exact (Subalgebra.range_val _).symm
  let q := Ideal.Quotient.mkₐ R (shifted I)
  let x : Fin n → Ring I := fun j => q (u j)
  have hxR : Algebra.adjoin R (Set.range x) = ⊤ := by
    have h := congrArg (Subalgebra.map q) hu
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] at h
    exact h
  have hx : Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ := by
    apply Subalgebra.restrictScalars_injective R
    rw [Algebra.Subalgebra.restrictScalars_adjoin, hxR, sup_top_eq, Subalgebra.restrictScalars_top]
  refine ⟨n, x, hx, ?_⟩
  intro j
  exact ⟨u j, ⟨⟨a j, hamem j⟩, rfl⟩, rfl⟩

end Lech.IdealGraded


namespace Lech.Grading
open SetLike MvPolynomial
variable {S B ι : Type*} [CommRing S] [CommRing B] [Algebra S B]
  (G : ℕ → Submodule S B) [GradedAlgebra G] (x : ι → B)

lemma aeval_mem (hx : ∀ i, x i ∈ G 1) {n : ℕ}
    {p : MvPolynomial ι S} (hp : p ∈ homogeneousSubmodule ι S n) :
    aeval x p ∈ G n := by
  classical
  rw [p.as_sum]
  rw [map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hn : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  rw [← hn]
  change (∏ i ∈ d.support, x i ^ d i) ∈ G (∑ i ∈ d.support, d i)
  simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using
    (SetLike.prod_pow_mem_graded G (fun _ : ι => 1) x d
      (F := d.support) (fun i _ => hx i))

attribute [local instance] MvPolynomial.gradedAlgebra
 
def polynomialMap (hx : ∀ i, x i ∈ G 1) : homogeneousSubmodule ι S →+*ᵍ G where
  toRingHom := (aeval x).toRingHom
  map_mem := aeval_mem G x hx

lemma polynomialMap_surjective (hx : ∀ i, x i ∈ G 1)
    (hgen : Algebra.adjoin S (Set.range x) = ⊤) :
    Function.Surjective (polynomialMap G x hx) := by
  exact (AlgHom.range_eq_top (aeval x)).mp
    (by simpa only [MvPolynomial.aeval_range] using hgen)
end Lech.Grading


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)
noncomputable instance gradeGradedAlgebra : GradedAlgebra (grade I) where
  toDecomposition := gradeDecomposition I
  one_mem := by
    refine ⟨1, ?_, map_one (Ideal.Quotient.mk (shifted I))⟩
    exact ⟨⟨1, by simp⟩, by apply Subtype.ext; change Polynomial.monomial 0 (1 : R) = 1; simp⟩
  mul_mem := fun _ _ _ _ hx hy => grade_mul I hx hy

variable {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z) = I)
def generator (j : ι) : Ring I :=
  Ideal.Quotient.mk (shifted I) (monomial I 1 ⟨z j, by
    rw [pow_one, ← hz]; exact Ideal.subset_span (Set.mem_range_self j)⟩)
lemma generator_mem (j : ι) : generator I z hz j ∈ grade I 1 :=
  ⟨_,⟨_,rfl⟩,rfl⟩

lemma generator_adjoin : Algebra.adjoin (R ⧸ I) (Set.range (generator I z hz)) = ⊤ := by
  let u : ι → reesAlgebra I := fun j => monomial I 1 ⟨z j, by
    rw [pow_one, ← hz]; exact Ideal.subset_span (Set.mem_range_self j)⟩
  have hupoly : Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (z j))) =
      reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← hz, Submodule.map_span, Algebra.adjoin_span,
      ← Set.range_comp]
    rfl
  have hu : Algebra.adjoin R (Set.range u) = ⊤ := by
    apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    change Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (z j))) = _
    rw [hupoly]
    exact (Subalgebra.range_val _).symm
  let q := Ideal.Quotient.mkₐ R (shifted I)
  have hxR : Algebra.adjoin R (Set.range (generator I z hz)) = ⊤ := by
    have h := congrArg (Subalgebra.map q) hu
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] at h
    exact h
  apply Subalgebra.restrictScalars_injective R
  rw [Algebra.Subalgebra.restrictScalars_adjoin, hxR, sup_top_eq, Subalgebra.restrictScalars_top]
attribute [local instance] MvPolynomial.gradedAlgebra
 
def polynomialMap : MvPolynomial.homogeneousSubmodule ι (R ⧸ I) →+*ᵍ grade I :=
  Grading.polynomialMap (grade I) (generator I z hz) (generator_mem I z hz)

lemma polynomialMap_surjective : Function.Surjective (polynomialMap I z hz) :=
  Grading.polynomialMap_surjective _ _ _ (generator_adjoin I z hz)
end Lech.IdealGraded


namespace Lech.Homogeneous

section
open HomogeneousLocalization SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]


instance module (U : Submonoid A) : Module R (HomogeneousLocalization G U) :=
  Function.Injective.module R (algebraMap (HomogeneousLocalization G U) (Localization U)).toAddMonoidHom
    (val_injective U) (val_smul U)

 
def fraction {f : A} {d : ℕ} (hf : f ∈ G d) (n : ℕ) :
    G (n*d) →ₗ[R] Away G f where
  toFun a := Away.mk G hf n a (by simpa only [nsmul_eq_mul, Nat.cast_id] using a.2)
  map_add' a b := by
    apply val_injective (Submonoid.powers f)
    simp only [Away.val_mk,val_add,Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' c a := by
    apply val_injective (Submonoid.powers f)
    simp only [Away.val_mk,val_smul,Submodule.coe_smul,RingHom.id_apply]
    exact (Localization.smul_mk _ _ _).symm

variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

def gradedMap (j : ℕ) : G j →ₗ[R] H j where
  toFun a := ⟨g a,map_mem g a.2⟩
  map_add' a b := by ext; exact map_add g _ _
  map_smul' r a := by ext; exact hg r a

def awayMap (f : A) : Away G f →ₗ[R] Away H (g f) where
  toFun := Away.map g f
  map_add' := map_add _
  map_smul' r a := by
    obtain ⟨a,rfl⟩ := HomogeneousLocalization.mk_surjective a
    change HomogeneousLocalization.map g _ (HomogeneousLocalization.mk (r • a)) = _
    simp only [HomogeneousLocalization.map_mk]
    congr 1
    ext
    · rfl
    · exact hg r a.num
    · rfl

@[simp] lemma awayMap_fraction {f : A} {d : ℕ} (hf : f ∈ G d) (n : ℕ)
    (a : G (n*d)) :
    awayMap G H g hg f (fraction G hf n a) =
      fraction H (map_mem g hf) n (gradedMap G H g hg (n*d) a) := by
  exact Away.map_mk g f hf n a (by simpa only [nsmul_eq_mul, Nat.cast_id] using a.2)

lemma gradedMap_surjective (hs : Function.Surjective g) (j : ℕ) :
    Function.Surjective (gradedMap G H g hg j) := by
  intro b
  obtain ⟨a,ha⟩ := hs b
  refine ⟨DirectSum.decompose G a j,?_⟩
  apply Subtype.ext
  change g (DirectSum.decompose G a j) = (b : B)
  rw [g.map_directSumDecompose,ha]
  exact DirectSum.decompose_of_mem_same H b.2

lemma awayMap_surjective {f : A} {d : ℕ} (hf : f ∈ G d)
    (hs : Function.Surjective g) : Function.Surjective (awayMap G H g hg f) := by
  intro x
  obtain ⟨n,b,hb,rfl⟩ := Away.mk_surjective H (map_mem g hf) x
  obtain ⟨a,ha⟩ := gradedMap_surjective G H g hg hs (n*d)
    ⟨b,by simpa only [nsmul_eq_mul,Nat.cast_id] using hb⟩
  refine ⟨fraction G hf n a,?_⟩
  rw [awayMap_fraction,ha]
  rfl


lemma kernel_fraction {f : A} {d : ℕ} (hf : f ∈ G d)
    (x : LinearMap.ker (awayMap G H g hg f)) :
    ∃ (n : ℕ) (a : LinearMap.ker (gradedMap G H g hg (n*d))),
      fraction G hf n a = (x : Away G f) := by
  obtain ⟨n,a,ha,hax⟩ := Away.mk_surjective G hf x
  have hz := x.2
  change awayMap G H g hg f x = 0 at hz
  rw [←hax] at hz
  change Away.map g f (Away.mk G hf n a ha) = 0 at hz
  rw [Away.map_mk] at hz
  have hv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk,val_zero,Localization.mk_eq_mk'] at hv
  obtain ⟨⟨s,hs⟩,he⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hv
  obtain ⟨k,rfl⟩ := hs
  have hmem : f^k*a ∈ G ((k+n)*d) := by
    rw [add_mul]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul,Nat.cast_id] using
      (pow_mem_graded k hf)) (by simpa only [nsmul_eq_mul,Nat.cast_id] using ha)
  have hker : gradedMap G H g hg ((k+n)*d) ⟨f^k*a,hmem⟩ = 0 := by
    apply Subtype.ext
    change g (f^k*a) = 0
    simpa only [map_mul,map_pow] using he
  refine ⟨k+n,⟨⟨f^k*a,hmem⟩,hker⟩,?_⟩
  rw [← hax]
  apply val_injective (Submonoid.powers f)
  simp only [fraction,LinearMap.coe_mk,AddHom.coe_mk,Away.val_mk]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

end


open HomogeneousLocalization SetLike Graded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d)

local instance awayAddCommGroup (f : A) : AddCommGroup (Away G f) :=
  (inferInstance : CommRing (Away G f)).toAddCommGroup

 
def kernelFraction (n : ℕ) :
    LinearMap.ker (gradedMap G H g hg (n*d)) →ₗ[R]
      LinearMap.ker (awayMap G H g hg f) :=
  ((fraction G hf n).comp (LinearMap.ker (gradedMap G H g hg (n*d))).subtype).codRestrict _ (by
    intro a
    change awayMap G H g hg f (fraction G hf n a) = 0
    rw [awayMap_fraction]
    have ha : gradedMap G H g hg (n*d) a = 0 := a.2
    rw [ha,map_zero])

lemma iSup_range_kernelFraction :
    (⨆ n, LinearMap.range (kernelFraction G H g hg hf n)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n,a,ha⟩ := kernel_fraction G H g hg hf x
  apply Submodule.mem_iSup_of_mem n
  exact ⟨a,Subtype.ext ha⟩

include hf in
 

theorem kernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hker : ∀ n, P (ModuleCat.of R (LinearMap.ker (gradedMap G H g hg n))))
    (hsum : ∀ (U : ℕ → Submodule R (LinearMap.ker (awayMap G H g hg f))),
      (∀ n, P (ModuleCat.of R ↥(U n))) → P (ModuleCat.of R ↥(⨆ n,U n : Submodule R (LinearMap.ker (awayMap G H g hg f))))) :
    P (ModuleCat.of R (LinearMap.ker (awayMap G H g hg f))) := by
  let U (n : ℕ) := LinearMap.range (kernelFraction G H g hg hf n)
  have hU (n : ℕ) : P (ModuleCat.of R ↥(U n)) := by
    let q : ModuleCat.of R (LinearMap.ker (gradedMap G H g hg (n*d))) ⟶
        ModuleCat.of R (U n) :=
      ModuleCat.ofHom (kernelFraction G H g hg hf n).rangeRestrict
    let : Epi q := (ModuleCat.epi_iff_surjective q).mpr
      (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
    exact P.prop_of_epi q (hker (n*d))
  have hu := hsum U hU
  have he : (⨆ n,U n) = ⊤ := iSup_range_kernelFraction G H g hg hf
  have hu' : P (ModuleCat.of R (⊤ : Submodule R (LinearMap.ker (awayMap G H g hg f)))) :=
    he ▸ hu
  exact P.prop_of_iso (LinearEquiv.ofTop (⊤ : Submodule R
    (LinearMap.ker (awayMap G H g hg f))) rfl).toModuleIso hu'

end Lech.Homogeneous


namespace Lech.Grading
open MvPolynomial
variable (S : Type*) [CommRing S]
def MonomialIndex (h n : ℕ) := {d : Fin h →₀ ℕ // d.degree = n}
noncomputable def indexEquiv (h n : ℕ) : MonomialIndex h n ≃ Sym (Fin h) n :=
  (Sym.equivNatSum (Fin h) n).symm
noncomputable instance indexFintype (h n : ℕ) : Fintype (MonomialIndex h n) :=
  Fintype.ofEquiv (Sym (Fin h) n) (indexEquiv h n).symm
lemma index_card (h n : ℕ) : Fintype.card (MonomialIndex h n) = h.multichoose n :=
  (Fintype.card_congr (indexEquiv h n)).trans (Sym.card_sym_fin_eq_multichoose h n)
 
noncomputable def homogeneousEquiv (h n : ℕ) :
    homogeneousSubmodule (Fin h) S n ≃ₗ[S] (MonomialIndex h n → S) :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin h) S n)).trans
    ((AddMonoidAlgebra.supportedEquivFinsupp (R := S) (S := S) {d : Fin h →₀ ℕ | d.degree=n}).trans
      (Finsupp.linearEquivFunOnFinite S S (MonomialIndex h n)))
end Lech.Grading

end

end OAI
