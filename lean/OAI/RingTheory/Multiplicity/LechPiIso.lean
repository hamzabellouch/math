import Mathlib
import OAI.RingTheory.Multiplicity.ActualCechTranspose

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech

section

section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v w u' v'
variable {A : Type u'} [Category.{v'} A] [Abelian A]
lemma pi_isoModSerre (P : ObjectProperty A) [P.IsSerreClass]
    {ι : Type w} [Finite ι] {M N : ι → A} [HasProduct M] [HasProduct N]
    (f : ∀ i, M i ⟶ N i) (hf : ∀ i, P.isoModSerre (f i)) :
    P.isoModSerre (Limits.Pi.map f) := by
  let Q := P.isoModSerre.Q
  let := ObjectProperty.SerreClassLocalization.abelian Q P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits Q P
  have (i : ι) : IsIso (Q.map (f i)) :=
    (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (f i)).mpr (hf i)
  have he : Q.map (Limits.Pi.map f) ≫ piComparison Q N =
      piComparison Q M ≫ Limits.Pi.map (fun i => Q.map (f i)) := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
    rw [← Q.map_comp, Limits.Pi.map_π, Q.map_comp]
    rw [← Category.assoc, piComparison_comp_π]
  have : IsIso (Q.map (Limits.Pi.map f) ≫ piComparison Q N) := by
    rw [he]
    infer_instance
  have : IsIso (Q.map (Limits.Pi.map f)) := IsIso.of_isIso_comp_right _ (piComparison Q N)
  exact (ObjectProperty.SerreClassLocalization.isIso_map_iff Q P (Limits.Pi.map f)).mp inferInstance

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    [HasProducts.{w} A] {ι : Type w} [Finite ι] (U : ι → C)
 

lemma cech_homology_isoModSerre (P : ObjectProperty A) [P.IsSerreClass]
    {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) (hf : ∀ X, P.isoModSerre (f.app X)) (n : ℕ) :
    P.isoModSerre (homologyMap ((cechComplexFunctor U).map f) n) := by
  apply homology_isoModSerre_of_termwise P
  intro j
  change P.isoModSerre (Limits.Pi.map (fun (a : Fin (j+1) → ι) => f.app (op (∏ᶜ (U ∘ a)))))
  exact pi_isoModSerre P _ (fun a => hf _)
end


open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Finite ι]
  {M N : ι → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

omit [Finite ι] in
lemma piLinear_factorization :
    ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (M i))).inv ≫
      Limits.Pi.map (fun i => ModuleCat.ofHom (f i)) ≫
      (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).hom := by
  apply (cancel_mono (ModuleCat.piIsoPi (fun i => ModuleCat.of R (N i))).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Limits.Pi.hom_ext
  intro i
  simp only [Category.assoc,Limits.Pi.map_π,
    ModuleCat.piIsoPi_inv_kernel_ι]
  rw [← Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  rfl

lemma piLinear_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hf : ∀ i, P.isoModSerre (ModuleCat.ofHom (f i))) :
    P.isoModSerre (ModuleCat.ofHom (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i)))) := by
  rw [piLinear_factorization]
  exact P.isoModSerre.comp_mem _ _
    (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ (pi_isoModSerre P _ hf) (P.isoModSerre_of_isIso _))

lemma isoModSerre_of_surjective_kernel
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hsurj : Function.Surjective f) (hk : P (ModuleCat.of R f.ker)) :
    P.isoModSerre (ModuleCat.ofHom f) := by
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  rw [P.isoModSerre_iff_of_epi]
  exact (P.prop_iff_of_iso (ModuleCat.kernelIsoKer (ModuleCat.ofHom f))).mpr hk
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
lemma homology_zeroClass_of_termwise_exactAt {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (hf : ∀ i, P.isoModSerre (f.f i)) (i : ι) (hi : K.ExactAt i) :
    P (L.homology i) := by
  have h := (homology_isoModSerre_of_termwise P f hf i).2
  have hz := (exactAt_iff_isZero_homology K i).mp hi
  have he := hz.eq_of_src (homologyMap f i) 0
  rw [he,P.epiModSerre_zero_iff] at h
  exact h
end Lech


namespace Lech.TwistedLocalization

section

section
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)

 
def fraction (t n : ℕ) : G (n*d+t) →ₗ[R] Localization.Away f where
  toFun a := Localization.mk (a : A) (⟨f^n, n, rfl⟩ : Submonoid.powers f)
  map_add' a b := by
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r a := by
    exact (Localization.smul_mk _ _ _).symm


def piece (t : ℕ) : Submodule R (Localization.Away f) :=
  ⨆ n : ℕ, LinearMap.range (fraction G (f := f) (d := d) t n)

omit [GradedAlgebra G] in
lemma fraction_mem (t n : ℕ) (a : G (n*d+t)) :
    fraction G (f := f) t n a ∈ piece G (f := f) (d := d) t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

include hf

lemma raise_fraction (t n k : ℕ) (a : G (n*d+t)) :
    ∃ b : G ((k+n)*d+t), fraction G (f := f) t (k+n) b =
      fraction G (f := f) t n a := by
  have hb : f^k*(a : A) ∈ G ((k+n)*d+t) := by
    rw [add_mul, add_assoc]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (pow_mem_graded k hf)) a.property
  refine ⟨⟨f^k*(a : A),hb⟩,?_⟩
  dsimp [fraction]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, pow_add]
  ring

lemma range_mono (t : ℕ) : Monotone (fun n : ℕ =>
    LinearMap.range (fraction G (f := f) (d := d) t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction G hf t n k a


lemma exists_fraction (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ∃ (n : ℕ) (a : G (n*d+t)), fraction G (f := f) t n a = (x : Localization.Away f) := by
  have hx := x.property
  change (x : Localization.Away f) ∈ (⨆ n, LinearMap.range (fraction G (f := f) (d := d) t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono G hf t).directed_le] at hx
  exact hx

omit hf
variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

 
def algHom : A →ₐ[R] B where
  toFun := g
  map_zero' := map_zero g
  map_one' := map_one g
  map_add' := map_add g
  map_mul' := map_mul g
  commutes' r := by
    simpa only [Algebra.smul_def, mul_one, map_one] using hg r (1 : A)

def gradedMap (j : ℕ) : G j →ₗ[R] H j where
  toFun a := ⟨g a,map_mem g a.property⟩
  map_add' a b := Subtype.ext (map_add g (a : A) (b : A))
  map_smul' r a := Subtype.ext (hg r a)

lemma gradedMap_surjective (hs : Function.Surjective g) (j : ℕ) :
    Function.Surjective (gradedMap G H g hg j) := by
  intro b
  obtain ⟨a,ha⟩ := hs b
  refine ⟨DirectSum.decompose G a j, ?_⟩
  apply Subtype.ext
  change g (DirectSum.decompose G a j) = (b : B)
  rw [g.map_directSumDecompose,ha]
  exact DirectSum.decompose_of_mem_same H b.property

def ambientMap : Localization.Away f →ₐ[R] Localization.Away (g f) := by
  letI : IsLocalization.Away ((algHom G H g hg) f) (Localization.Away (g f)) :=
    inferInstanceAs (IsLocalization.Away (g f) (Localization.Away (g f)))
  exact IsLocalization.Away.mapₐ _ _ (algHom G H g hg) f

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma ambientMap_fraction (t n : ℕ) (a : G (n*d+t)) :
    ambientMap G H g hg (fraction G (f := f) t n a) =
      fraction H (f := g f) t n (gradedMap G H g hg (n*d+t) a) := by
  simp only [ambientMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    fraction, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  simp only [gradedMap, LinearMap.coe_mk, AddHom.coe_mk, algHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_pow]

include hf
omit [GradedAlgebra H] in
lemma ambientMap_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientMap G H g hg (x : Localization.Away f) ∈ piece H (f := g f) (d := d) t := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  rw [← ha, ambientMap_fraction]
  exact fraction_mem H t n _

def pieceMap (t : ℕ) : piece G (f := f) (d := d) t →ₗ[R]
    piece H (f := g f) (d := d) t :=
  ((ambientMap G H g hg).toLinearMap.comp (piece G (f := f) (d := d) t).subtype).codRestrict
    _ (ambientMap_mem G hf H g hg t)

def pieceFraction (t n : ℕ) : G (n*d+t) →ₗ[R] piece G (f := f) (d := d) t :=
  (fraction G (f := f) t n).codRestrict _ (fraction_mem G t n)

omit [GradedAlgebra H] in
@[simp] lemma pieceMap_fraction (t n : ℕ) (a : G (n*d+t)) :
    pieceMap G hf H g hg t (pieceFraction G (f := f) t n a) =
      pieceFraction H (f := g f) t n (gradedMap G H g hg (n*d+t) a) := by
  apply Subtype.ext
  exact ambientMap_fraction G H g hg t n a

lemma pieceMap_surjective (hs : Function.Surjective g) (t : ℕ) :
    Function.Surjective (pieceMap G hf H g hg t) := by
  intro x
  obtain ⟨n,b,hb⟩ := exists_fraction H (map_mem g hf) t x
  obtain ⟨a,ha⟩ := gradedMap_surjective G H g hg hs (n*d+t) b
  refine ⟨pieceFraction G (f := f) t n a, ?_⟩
  rw [pieceMap_fraction,ha]
  exact Subtype.ext hb

omit [GradedAlgebra H] in
 

lemma kernel_fraction (t : ℕ) (x : LinearMap.ker (pieceMap G hf H g hg t)) :
    ∃ (n : ℕ) (a : LinearMap.ker (gradedMap G H g hg (n*d+t))),
      pieceFraction G (f := f) t n a = (x : piece G (f := f) (d := d) t) := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  have hz := congrArg Subtype.val x.property
  change ambientMap G H g hg ((x : piece G (f := f) (d := d) t) : Localization.Away f) = 0 at hz
  rw [←ha, ambientMap_fraction] at hz
  simp only [fraction, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_eq_mk'] at hz
  obtain ⟨⟨v,hv⟩,he⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hz
  obtain ⟨k,rfl⟩ := hv
  change (g f)^k * g (a : A) = 0 at he
  have hm : f^k*(a : A) ∈ G ((k+n)*d+t) := by
    rw [add_mul, add_assoc]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (pow_mem_graded k hf)) a.property
  have hk : gradedMap G H g hg ((k+n)*d+t) ⟨f^k*(a : A),hm⟩ = 0 := by
    apply Subtype.ext
    change g (f^k*(a : A)) = 0
    simpa only [map_mul,map_pow] using he
  refine ⟨k+n,⟨⟨f^k*(a : A),hm⟩,hk⟩,?_⟩
  apply Subtype.ext
  rw [←ha]
  change Localization.mk _ _ = Localization.mk _ _
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

omit [GradedAlgebra H] in
 

lemma kernel_fraction_eq (t : ℕ) (x : piece G (f := f) (d := d) t)
    (hx : pieceMap G hf H g hg t x=0) :
    ∃ (n : ℕ) (a : G (n*d+t)), g (a:A)=0 ∧ pieceFraction G (f := f) t n a=x := by
  obtain ⟨n,a,ha⟩ := kernel_fraction G hf H g hg t ⟨x,hx⟩
  refine ⟨n,a.val,?_,ha⟩
  exact congrArg Subtype.val a.property

 
def kernelFraction (t n : ℕ) :
    LinearMap.ker (gradedMap G H g hg (n*d+t)) →ₗ[R]
      LinearMap.ker (pieceMap G hf H g hg t) :=
  ((pieceFraction G (f := f) t n).comp
    (LinearMap.ker (gradedMap G H g hg (n*d+t))).subtype).codRestrict _ (by
      intro a
      change pieceMap G hf H g hg t (pieceFraction G (f := f) t n a) = 0
      rw [pieceMap_fraction]
      have ha : gradedMap G H g hg (n*d+t) a = 0 := a.property
      rw [ha,map_zero])

omit [GradedAlgebra H] in
lemma iSup_range_kernelFraction (t : ℕ) :
    (⨆ n, LinearMap.range (kernelFraction G hf H g hg t n)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n,a,ha⟩ := kernel_fraction G hf H g hg t x
  exact Submodule.mem_iSup_of_mem n ⟨a,Subtype.ext ha⟩

open CategoryTheory CategoryTheory.Limits
local instance kernelAdd (t : ℕ) : AddCommGroup (LinearMap.ker (pieceMap G hf H g hg t)) :=
  Submodule.addCommGroup (R := R) (M := piece G (f := f) (d := d) t)
    (LinearMap.ker (pieceMap G hf H g hg t))
local instance kernelModule (t : ℕ) : Module R (LinearMap.ker (pieceMap G hf H g hg t)) :=
  Submodule.module (R := R) (M := piece G (f := f) (d := d) t)
    (LinearMap.ker (pieceMap G hf H g hg t))
attribute [local irreducible] pieceMap gradedMap kernelFraction
omit [GradedAlgebra H] in
 

theorem kernel_property (t : ℕ) (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hker : ∀ n, P (ModuleCat.of R (LinearMap.ker (gradedMap G H g hg n))))
    (hsum : ∀ (U : ℕ → Submodule R (LinearMap.ker (pieceMap G hf H g hg t))),
      (∀ n, P (ModuleCat.of R ↥(U n))) →
        P (ModuleCat.of R ↥(⨆ n,U n : Submodule R (LinearMap.ker (pieceMap G hf H g hg t))))) :
    P (ModuleCat.of R (LinearMap.ker (pieceMap G hf H g hg t))) := by
  let U (n : ℕ) := LinearMap.range (kernelFraction G hf H g hg t n)
  have hU (n : ℕ) : P (ModuleCat.of R ↥(U n)) := by
    let q : ModuleCat.of R (LinearMap.ker (gradedMap G H g hg (n*d+t))) ⟶
        ModuleCat.of R (U n) := ModuleCat.ofHom (kernelFraction G hf H g hg t n).rangeRestrict
    let : Epi q := (ModuleCat.epi_iff_surjective q).mpr
      (by rintro ⟨y,a,rfl⟩; exact ⟨a,rfl⟩)
    exact P.prop_of_epi q (hker (n*d+t))
  have hu := hsum U hU
  have he : (⨆ n,U n) = ⊤ := iSup_range_kernelFraction G hf H g hg t
  have hu' : P (ModuleCat.of R (⊤ : Submodule R (LinearMap.ker (pieceMap G hf H g hg t)))) :=
    he ▸ hu
  exact P.prop_of_iso (LinearEquiv.ofTop (⊤ : Submodule R
    (LinearMap.ker (pieceMap G hf H g hg t))) rfl).toModuleIso hu'

end


open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]


def ambientRestriction (f q : A) : Localization.Away f →ₐ[R] Localization.Away (f*q) :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.algHom R A (Localization.Away (f*q)))
    (IsLocalization.Away.isUnit_of_dvd (f*q) (dvd_mul_right f q))

@[simp] lemma ambientRestriction_algebraMap (f q a : A) :
    ambientRestriction (R := R) f q (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away (f*q)) a := by
  exact IsLocalization.Away.lift_eq f
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (f*q))
      (f*q) (dvd_mul_right f q)) a

lemma ambientRestriction_mk (f q a : A) (n : ℕ) :
    ambientRestriction (R := R) f q
      (Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f)) =
    Localization.mk (a*q^n) (⟨(f*q)^n,n,rfl⟩ : Submonoid.powers (f*q)) := by
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change ambientRestriction (R := R) f q (IsLocalization.mk' _ a _) *
    algebraMap A (Localization.Away (f*q)) ((f*q)^n) = _
  rw [mul_pow,map_mul,←mul_assoc,
    ←ambientRestriction_algebraMap (R := R) f q (f^n),←map_mul,
    IsLocalization.mk'_spec,ambientRestriction_algebraMap,map_mul]

variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q : A} {d e : ℕ} (hf : f ∈ G d) (hq : q ∈ G e)

include hq in
lemma restriction_fraction (t n : ℕ) (a : G (n*d+t)) :
    ∃ b : G (n*(d+e)+t),
      ambientRestriction (R := R) f q (fraction G (f := f) t n a) =
        fraction G (f := f*q) t n b := by
  have hb : (a : A)*q^n ∈ G (n*(d+e)+t) := by
    have heq : n*d+t+n*e = n*(d+e)+t := by ring
    simpa only [nsmul_eq_mul,Nat.cast_id,heq] using
      mul_mem_graded a.property (pow_mem_graded n hq)
  exact ⟨⟨(a : A)*q^n,hb⟩,ambientRestriction_mk f q a n⟩

include hf hq in
lemma ambientRestriction_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientRestriction (R := R) f q (x : Localization.Away f) ∈
      piece G (f := f*q) (d := d+e) t := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  obtain ⟨b,hb⟩ := restriction_fraction G hq t n a
  rw [←ha,hb]
  exact fraction_mem G t n b


def pieceRestriction (t : ℕ) : piece G (f := f) (d := d) t →ₗ[R]
    piece G (f := f*q) (d := d+e) t :=
  ((ambientRestriction (R := R) f q).toLinearMap.comp
    (piece G (f := f) (d := d) t).subtype).codRestrict _
      (ambientRestriction_mem G hf hq t)

@[simp] lemma pieceRestriction_val (t : ℕ) (x : piece G (f := f) (d := d) t) :
    (pieceRestriction G hf hq t x : Localization.Away (f*q)) =
      ambientRestriction (R := R) f q x := rfl

end


open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

 
def ambientTo {f q : A} (h : f ∣ q) : Localization.Away f →ₐ[R] Localization.Away q :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.algHom R A (Localization.Away q))
    (IsLocalization.Away.isUnit_of_dvd q h)

@[simp] lemma ambientTo_algebraMap {f q : A} (h : f ∣ q) (a : A) :
    ambientTo (R := R) h (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away q) a :=
  IsLocalization.Away.lift_eq f (IsLocalization.Away.isUnit_of_dvd q h) a

lemma ambientTo_comp {f q r : A} (hfq : f ∣ q) (hqr : q ∣ r) :
    (ambientTo (R := R) hqr).comp (ambientTo hfq) = ambientTo (hfq.trans hqr) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientTo hqr (ambientTo hfq (algebraMap A _ a)) =
    ambientTo (hfq.trans hqr) (algebraMap A _ a)
  simp only [ambientTo_algebraMap]

lemma ambientTo_self (f : A) : ambientTo (R := R) (dvd_refl f) = AlgHom.id R _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientTo (dvd_refl f) (algebraMap A _ a) = algebraMap A _ a
  exact ambientTo_algebraMap _ a

lemma ambientTo_mk {f q c : A} (hfc : f*c=q) (a : A) (n : ℕ) :
    ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩)
      (Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f)) =
    Localization.mk (a*c^n) (⟨q^n,n,rfl⟩ : Submonoid.powers q) := by
  subst q
  exact ambientRestriction_mk f c a n

variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

include hf hc hdeg in
lemma ambientTo_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩) x ∈
      piece G (f := q) (d := e) t := by
  subst q; subst e
  exact ambientRestriction_mem G hf hc t x

 
def pieceTo (t : ℕ) : piece G (f := f) (d := d) t →ₗ[R]
    piece G (f := q) (d := e) t :=
  ((ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩)).toLinearMap.comp
    (piece G (f := f) (d := d) t).subtype).codRestrict _
      (ambientTo_mem G hf hc hfc hdeg t)

@[simp] lemma pieceTo_val (t : ℕ) (x : piece G (f := f) (d := d) t) :
    (pieceTo G hf hc hfc hdeg t x : Localization.Away q) =
      ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩) x := rfl

variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

omit [GradedAlgebra G] [GradedAlgebra H] in
@[simp] lemma ambientMap_algebraMap {f : A} (a : A) :
    ambientMap G H g hg (algebraMap A (Localization.Away f) a) =
      algebraMap B (Localization.Away (g f)) (g a) := by
  simp only [ambientMap,IsLocalization.Away.mapₐ_apply,IsLocalization.Away.map,
    IsLocalization.map_eq,algHom,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma ambientMap_naturality {f q : A} (hfq : f ∣ q) :
    (ambientMap G H g hg (f := q)).comp (ambientTo (R := R) hfq) =
      (ambientTo (R := R) (map_dvd g hfq)).comp (ambientMap G H g hg (f := f)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientMap G H g hg (ambientTo hfq (algebraMap A _ a)) =
    ambientTo (map_dvd g hfq) (ambientMap G H g hg (algebraMap A _ a))
  simp only [ambientTo_algebraMap,ambientMap_algebraMap]

end Lech.TwistedLocalization

end

end OAI
