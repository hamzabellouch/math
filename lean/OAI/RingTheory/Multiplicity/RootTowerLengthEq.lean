import Mathlib
import OAI.RingTheory.Multiplicity.NormalizedLengthTrivialRelation

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable {A D : Type*} [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma length_eq_of_residue_surjective
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M] :
    Module.length A M = Module.length D M := by
  rw [IsLocalRing.length_restrictScalars A D M,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp

end Lech.RootTower


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k D : Type*) [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

 

lemma normalizedLength_stage_quotient
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (H : Ideal D) (n : ℕ) :
    let : Algebra (MvPowerSeries σ k) (PerfectClosure (MvPowerSeries σ k) p) :=
      (rootMap (MvPowerSeries σ k) p n).toAlgebra
    normalizedLength σ k p (((PerfectClosure (MvPowerSeries σ k) p) ⊗[MvPowerSeries σ k] D) ⧸
      H.map ((Algebra.TensorProduct.includeRight (R := MvPowerSeries σ k)
        (A := PerfectClosure (MvPowerSeries σ k) p)).toRingHom.comp (iterateFrobenius D p n))) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let J := H.map (iterateFrobenius D p n)
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) P D P J
  have he := (regularTower σ k p).length_eq_of_equiv e.toLinearEquiv
  change normalizedLength σ k p (P ⊗[A] (D ⧸ J)) =
    normalizedLength σ k p ((P ⊗[A] D) ⧸ J.map (Algebra.TensorProduct.includeRight (R := A) (A := P))) at he
  change normalizedLength σ k p ((P ⊗[A] D) ⧸ _) = _
  rw [← Ideal.map_map]
  change normalizedLength σ k p ((P ⊗[A] D) ⧸
    J.map (Algebra.TensorProduct.includeRight (R := A) (A := P))) = _
  rw [← he,normalizedLength_rootBaseChange]
  congr 1
  exact congrArg ENat.toENNReal (length_eq_of_residue_surjective hres (D ⧸ J))

end Lech.RootTower


namespace Lech.RootTower
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

lemma rootMap_pow (n : ℕ) (a : A) :
    (rootMap A p n a)^(p^n) = PerfectClosure.of A p a := by
  exact (iterate_frobenius p n _).symm.trans
    (PerfectClosure.iterate_frobenius_mk A p n a)

def perfectMap (f : A →+* B) : PerfectClosure A p →+* PerfectClosure B p :=
  PerfectRing.lift (PerfectClosure.of A p) ((PerfectClosure.of B p).comp f) p

lemma perfectMap_root (f : A →+* B) (n : ℕ) (a : A) :
    perfectMap p f (rootMap A p n a) = rootMap B p n (f a) := by
  apply (injective_frobenius (PerfectClosure B p) p).iterate n
  rw [iterate_frobenius, iterate_frobenius, ← map_pow, rootMap_pow, rootMap_pow]
  exact PerfectRing.lift_comp_apply _ _ _ _

lemma perfectMap_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (perfectMap p f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p x
  change perfectMap p f (rootMap A p n a) = 0 at hx
  rw [perfectMap_root, ← (rootMap B p n).map_zero] at hx
  have ha : a = 0 := hf ((rootMap_injective B p n hx).trans f.map_zero.symm)
  change rootMap A p n a = 0
  rw [ha, map_zero]

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime] [CharP A p]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [CharP K p]

instance perfectDomain : IsDomain (PerfectClosure A p) :=
  Function.Injective.isDomain (perfectMap p (algebraMap A (FractionRing A)))
    (perfectMap_injective p _ (IsFractionRing.injective _ _))

instance perfectFractionAlgebra : Algebra (PerfectClosure A p) (PerfectClosure K p) :=
  (perfectMap p (algebraMap A K)).toAlgebra

instance perfectFraction : IsFractionRing (PerfectClosure A p) (PerfectClosure K p) := by
  let : FaithfulSMul (PerfectClosure A p) (PerfectClosure K p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (perfectMap_injective p _ (IsFractionRing.injective _ _))
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨n,x⟩,rfl⟩ := PerfectClosure.mk_surjective K p z
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective A x
  refine ⟨rootMap A p n a, rootMap A p n b, ?_⟩
  change rootMap K p n (algebraMap A K a / algebraMap A K b) =
    perfectMap p (algebraMap A K) _ / perfectMap p (algebraMap A K) _
  rw [perfectMap_root, perfectMap_root, map_div₀]

instance perfectAlgebra : Algebra A (PerfectClosure A p) := (PerfectClosure.of A p).toAlgebra

instance perfectIntegral : Algebra.IsIntegral A (PerfectClosure A p) where
  isIntegral x := by
    obtain ⟨n,a,ha⟩ := IsPRadical.pow_mem (PerfectClosure.of A p) p x
    apply IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n)
    rw [← ha]
    exact isIntegral_algebraMap

instance perfectNormal [IsIntegrallyClosed A] : IsIntegrallyClosed (PerfectClosure A p) := by
  let K := FractionRing A
  let Q := PerfectClosure K p
  let : Algebra A Q := ((PerfectClosure.of K p).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (PerfectClosure A p) Q := IsScalarTower.of_algebraMap_eq' (by
    exact (PerfectRing.lift_comp _ _ _).symm)
  apply (isIntegrallyClosed_iff Q).mpr
  intro x hx
  have hxA : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨n,y,hy⟩ := IsPRadical.pow_mem (PerfectClosure.of K p) p x
  have hyi : IsIntegral A y := by
    apply IsIntegral.tower_bot (R := A) (PerfectClosure.of K p).injective
    change IsIntegral A (PerfectClosure.of K p y)
    rw [hy]
    exact hxA.pow _
  obtain ⟨a,ha⟩ := (isIntegrallyClosed_iff K).mp (inferInstance : IsIntegrallyClosed A) hyi
  refine ⟨rootMap A p n a, ?_⟩
  apply (injective_frobenius Q p).iterate n
  rw [iterate_frobenius, iterate_frobenius, ← map_pow, rootMap_pow]
  change perfectMap p (algebraMap A K) (PerfectClosure.of A p a) = x^(p^n)
  rw [show perfectMap p (algebraMap A K) (PerfectClosure.of A p a) =
      PerfectClosure.of K p (algebraMap A K a) from PerfectRing.lift_comp_apply _ _ _ _]
  rw [ha, hy]

end Lech.RootTower


namespace Lech.RootTower
open Module
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

instance perfectBaseAlgebra : Algebra K (PerfectClosure L p) :=
  ((PerfectClosure.of L p).comp (algebraMap K L)).toAlgebra

instance perfectBaseTower : IsScalarTower K L (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance perfectExtensionTower : IsScalarTower K (PerfectClosure K p) (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm

def perfectOf : L →ₐ[K] PerfectClosure L p where
  __ := PerfectClosure.of L p
  commutes' _ := rfl

lemma perfect_span [FiniteDimensional K L] :
    Submodule.span (PerfectClosure K p) (Set.range (PerfectClosure.of L p)) = ⊤ := by
  let f := perfectOf K L p
  let S := Algebra.adjoin (PerfectClosure K p) (f.range : Set (PerfectClosure L p))
  let b := (Module.Free.chooseBasis K L).map (AlgEquiv.ofInjective f f.injective).toLinearEquiv
  have hS : S.toSubmodule.FG := by
    rw [show S.toSubmodule = Submodule.span (PerfectClosure K p)
      (Set.range fun i => ((b i : f.range) : PerfectClosure L p)) from
      f.range.adjoin_eq_span_basis _ b]
    exact Submodule.fg_span (Set.finite_range _)
  have : FiniteDimensional (PerfectClosure K p) S :=
    (Submodule.fg_iff_finiteDimensional S.toSubmodule).mp hS
  let E := Algebra.IsAlgebraic.toIntermediateField S
  have : FiniteDimensional (PerfectClosure K p) E := ‹FiniteDimensional (PerfectClosure K p) S›
  let : PerfectField E := Algebra.IsAlgebraic.perfectField (PerfectClosure K p)
  have hE : ∀ x : PerfectClosure L p, x ∈ E := by
    intro x
    obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective L p x
    have ha : PerfectClosure.of L p a ∈ E := Algebra.subset_adjoin ⟨a,rfl⟩
    obtain ⟨y,hy⟩ := (surjective_frobenius E p).iterate n ⟨_,ha⟩
    have hp : (y : PerfectClosure L p)^(p^n) = PerfectClosure.of L p a := by
      exact congrArg Subtype.val (by simpa only [iterate_frobenius] using hy)
    have heq : (y : PerfectClosure L p) = rootMap L p n a := by
      apply (injective_frobenius (PerfectClosure L p) p).iterate n
      rw [iterate_frobenius, iterate_frobenius, hp, rootMap_pow]
    change rootMap L p n a ∈ E
    rw [← heq]
    exact y.property
  apply top_unique
  intro x _
  have hx : x ∈ S.toSubmodule := hE x
  rw [show S.toSubmodule = Submodule.span (PerfectClosure K p)
    (Set.range fun i => ((b i : f.range) : PerfectClosure L p)) from
    f.range.adjoin_eq_span_basis _ b] at hx
  apply (Submodule.span_mono (s := Set.range fun i => ((b i : f.range) : PerfectClosure L p)) (t := Set.range (PerfectClosure.of L p)) ?_) hx
  rintro x ⟨i,rfl⟩
  exact (b i).property

lemma perfect_basis_independent [Algebra.IsSeparable K L] {ι : Type*} (b : Basis ι K L) :
    LinearIndependent (PerfectClosure K p) (fun i => PerfectClosure.of L p (b i)) := by
  let : IsPurelyInseparable K (PerfectClosure K p) :=
    (isPurelyInseparable_iff_pow_mem K p).mpr (by
      intro x
      change ∃ n, x ^ p ^ n ∈ (PerfectClosure.of K p).range
      exact IsPRadical.pow_mem (PerfectClosure.of K p) p x)
  apply LinearIndependent.map_of_isPurelyInseparable_of_isSeparable (F := K)
  · intro i
    exact (Algebra.IsSeparable.isSeparable K (b i)).map (perfectOf K L p) (perfectOf K L p).injective
  · exact b.linearIndependent.map' (perfectOf K L p).toLinearMap
      (LinearMap.ker_eq_bot.mpr (perfectOf K L p).injective)




lemma perfect_basis_span [FiniteDimensional K L] {ι : Type*} [Fintype ι] (b : Basis ι K L) :
    Submodule.span (PerfectClosure K p) (Set.range fun i => PerfectClosure.of L p (b i)) = ⊤ := by
  apply top_unique
  rw [← perfect_span K L p]
  apply Submodule.span_le.mpr
  rintro x ⟨l,rfl⟩
  rw [← b.sum_repr l, map_sum]
  apply Submodule.sum_mem
  intro i _
  change (perfectOf K L p) ((b.repr l i) • b i) ∈ _
  rw [map_smul]
  rw [← IsScalarTower.algebraMap_smul (PerfectClosure K p)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

noncomputable def perfectBasis [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (b : Basis ι K L) : Basis ι (PerfectClosure K p) (PerfectClosure L p) :=
  Basis.mk (perfect_basis_independent K L p b) (le_of_eq (perfect_basis_span K L p b).symm)

lemma perfectBasis_apply [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (b : Basis ι K L) (i : ι) :
    perfectBasis K L p b i = PerfectClosure.of L p (b i) := by
  simp [perfectBasis]

instance perfectExtensionFinite [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteDimensional (PerfectClosure K p) (PerfectClosure L p) :=
  Module.Finite.of_basis (perfectBasis K L p (Module.Free.chooseBasis K L))

end Lech.RootTower


namespace Lech.TraceConductor
open Algebra Module

variable {A E : Type*} [CommRing A] [CommRing E] [Algebra A E]

 
lemma finite_denominators (B : Subalgebra A E)
    (hden : ∀ x : E, ∃ a : A, a ≠ 0 ∧ a • x ∈ B)
    [IsDomain A] {ι : Type*} [Finite ι] (v : ι → E) :
    ∃ a : A, a ≠ 0 ∧ ∀ i, a • v i ∈ B := by
  classical
  have hfin (s : Finset ι) : ∃ a : A, a ≠ 0 ∧ ∀ i ∈ s, a • v i ∈ B := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨a, ha, hva⟩ := hden (v i)
        obtain ⟨b, hb, hvb⟩ := ih
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [mul_comm a b, mul_smul]
          exact B.smul_mem hva b
        · rw [mul_smul]
          exact B.smul_mem (hvb j hj) a
  let := Fintype.ofFinite ι
  simpa only [Finset.mem_univ, forall_true_left] using hfin Finset.univ

variable (A K E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]

include K in
 

theorem exists_conductor (B : Subalgebra A E)
    (hden : ∀ x : E, ∃ a : A, a ≠ 0 ∧ a • x ∈ B) :
    ∃ g : A, g ≠ 0 ∧ ∀ c : E, IsIntegral A c → g • c ∈ B := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K E
  obtain ⟨g, hg, hgb⟩ := finite_denominators B hden b.traceDual
  refine ⟨g, hg, fun c hc => ?_⟩
  have hspan : c ∈ Submodule.span A (Set.range b.traceDual) := by
    apply integralClosure_le_span_dualBasis b hb
    exact hc
  clear hc
  induction hspan using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hgb i
  | zero => simp
  | add x y hx hy ihx ihy => simpa [smul_add] using B.add_mem ihx ihy
  | smul a x hx ih =>
      rw [smul_comm g a]
      exact B.smul_mem ih a

end Lech.TraceConductor


namespace Lech.TraceConductor
open Module
variable {A K E : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]

lemma denominator_of_span (B : Subalgebra A E) {s : Set E}
    (hden : ∀ x ∈ s, ∃ a : A, a ≠ 0 ∧ a • x ∈ B)
    {x : E} (hx : x ∈ Submodule.span K s) : ∃ a : A, a ≠ 0 ∧ a • x ∈ B := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hden x hx
  | zero => exact ⟨1,one_ne_zero,by simp⟩
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      refine ⟨a*b,mul_ne_zero ha hb,?_⟩
      rw [smul_add]
      apply B.add_mem
      · rw [mul_comm a b,mul_smul]
        exact B.smul_mem hax b
      · rw [mul_smul]
        exact B.smul_mem hby a
  | smul t x hx ih =>
      obtain ⟨a,ha,hax⟩ := ih
      obtain ⟨u,v,hv,rfl⟩ := IsFractionRing.div_surjective A t
      have hv : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
      refine ⟨v*a,mul_ne_zero hv ha,?_⟩
      have hv' : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hv
      have heq : (v*a) • ((algebraMap A K u / algebraMap A K v) • x) = u • (a • x) := by
        rw [← IsScalarTower.algebraMap_smul K (v*a), ← IsScalarTower.algebraMap_smul K u,
          ← IsScalarTower.algebraMap_smul K a, map_mul, smul_smul, smul_smul]
        congr 1
        field_simp
      rw [heq]
      exact B.smul_mem hax u

variable {D : Type*} [CommRing D] [IsDomain D] [Algebra A D] [Algebra D E]
  [IsFractionRing D E] [IsScalarTower A D E] [Algebra.IsAlgebraic A D]

omit [IsDomain A] in
lemma denominator_fraction (x : E) :
    ∃ a : A, a ≠ 0 ∧ ∃ d : D, a • x = algebraMap D E d := by
  obtain ⟨u,v,hv,rfl⟩ := IsFractionRing.div_surjective D x
  have hv : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
  obtain ⟨y,a,ha,h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul A u hv
  refine ⟨a,ha,y,?_⟩
  have hv' : algebraMap D E v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D E)).mpr hv
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hv', ← map_mul]
  have hh := congrArg (algebraMap D E) h
  simpa only [Algebra.smul_def,map_mul,← IsScalarTower.algebraMap_apply,mul_comm] using hh

end Lech.TraceConductor


namespace Lech.RootTower
variable {A B C : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
  [CommRing C] [IsReduced C] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]

lemma perfectMap_comp (f : A →+* B) (g : B →+* C) :
    (perfectMap p g).comp (perfectMap p f) = perfectMap p (g.comp f) := by
  ext x
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p x
  change perfectMap p g (perfectMap p f (rootMap A p n a)) =
    perfectMap p (g.comp f) (rootMap A p n a)
  simp only [perfectMap_root,RingHom.comp_apply]

omit [IsReduced A] [IsReduced B] in
lemma perfectMap_of (f : A →+* B) (a : A) :
    perfectMap p f (PerfectClosure.of A p a) = PerfectClosure.of B p (f a) :=
  PerfectRing.lift_comp_apply _ _ _ _

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

instance perfectOriginalAlgebra : Algebra A (PerfectClosure L p) :=
  ((PerfectClosure.of L p).comp (algebraMap A L)).toAlgebra
instance perfectOriginalTower : IsScalarTower A L (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' rfl
instance perfectOriginalRootTower : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
  IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm

variable (K : Type*) [Field K] [CharP K p] [Algebra A K] [Algebra K L] [IsScalarTower A K L]
instance perfectScalarTower :
    IsScalarTower (PerfectClosure A p) (PerfectClosure K p) (PerfectClosure L p) := by
  apply IsScalarTower.of_algebraMap_eq'
  change perfectMap p (algebraMap A L) =
    (perfectMap p (algebraMap K L)).comp (perfectMap p (algebraMap A K))
  rw [perfectMap_comp,← IsScalarTower.algebraMap_eq]

end Lech.RootTower


namespace Lech.TraceConductor
open Lech.RootTower
variable (A D K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing D] [IsDomain D] [Field K] [Field L]
  [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsIntegral A D]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p] [CharP K p] [CharP L p]

 
def perfectOrder : Subalgebra (PerfectClosure A p) (PerfectClosure L p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range ((PerfectClosure.of L p).comp (algebraMap D L)))

include K in
omit [CharP D p] in
 
theorem exists_perfect_conductor :
    ∃ g : A, g ≠ 0 ∧ ∀ c : PerfectClosure L p, IsIntegral (PerfectClosure A p) c →
      (PerfectClosure.of A p g) • c ∈ perfectOrder A D L p := by
  let P := PerfectClosure A p
  let Q := PerfectClosure K p
  let E := PerfectClosure L p
  let B := perfectOrder A D L p
  have hden0 : ∀ x ∈ Set.range (PerfectClosure.of L p), ∃ a : P, a ≠ 0 ∧ a • x ∈ B := by
    rintro x ⟨l,rfl⟩
    obtain ⟨a,ha,d,hd⟩ := denominator_fraction (A := A) (D := D) l
    refine ⟨PerfectClosure.of A p a,?_,?_⟩
    · change rootMap A p 0 a ≠ 0
      exact (map_ne_zero_iff _ (rootMap_injective A p 0)).mpr ha
    · change perfectMap p (algebraMap A L) (PerfectClosure.of A p a) * PerfectClosure.of L p l ∈ B
      rw [perfectMap_of, ← map_mul]
      rw [show algebraMap A L a * l = algebraMap D L d from by simpa only [Algebra.smul_def] using hd]
      exact Algebra.subset_adjoin ⟨d,rfl⟩
  have hden : ∀ x : E, ∃ a : P, a ≠ 0 ∧ a • x ∈ B := by
    intro x
    apply denominator_of_span (K := Q) B hden0
    rw [perfect_span K L p]
    trivial
  obtain ⟨g,hg,hgc⟩ := exists_conductor P Q E B hden
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p g
  have hn : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  refine ⟨a,?_,fun c hc => ?_⟩
  · intro ha
    apply hg
    change rootMap A p n a = 0
    rw [ha,map_zero]
  · have hh : PerfectClosure.of A p a = (rootMap A p n a)^(p^n-1) * rootMap A p n a := by
      rw [← rootMap_pow p n a, ← pow_succ, Nat.sub_add_cancel hn]
    rw [hh,mul_smul]
    exact B.smul_mem (hgc c hc) _

end Lech.TraceConductor
end

end OAI
