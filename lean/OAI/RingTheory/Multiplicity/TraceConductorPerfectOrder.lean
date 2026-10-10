import Mathlib
import OAI.RingTheory.Multiplicity.RootTowerLengthEq

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
namespace Lech.TraceConductor
open Lech.RootTower
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A L] [Algebra D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
def perfectOrderAt (n : ℕ) : Subalgebra (PerfectClosure A p) (PerfectClosure L p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range ((rootMap L p n).comp (algebraMap D L)))

omit [IsDomain A] [IsDomain D] in
lemma perfectOrderAt_zero : perfectOrderAt A D L p 0 = perfectOrder A D L p := rfl

omit [IsDomain A] [IsDomain D] in
lemma perfectOrder_roots (n : ℕ) {x : PerfectClosure L p} (hx : x ∈ perfectOrder A D L p) :
    ∃ y ∈ perfectOrderAt A D L p n, y^(p^n) = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨d,rfl⟩ := hx
      exact ⟨rootMap L p n (algebraMap D L d),Algebra.subset_adjoin ⟨d,rfl⟩,rootMap_pow p n _⟩
  | algebraMap a =>
      obtain ⟨b,hb⟩ := (surjective_frobenius (PerfectClosure A p) p).iterate n a
      refine ⟨algebraMap (PerfectClosure A p) (PerfectClosure L p) b,
        (perfectOrderAt A D L p n).algebraMap_mem b,?_⟩
      rw [← map_pow,show b^(p^n) = a from by simpa only [iterate_frobenius] using hb]
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      exact ⟨a+b,(perfectOrderAt A D L p n).add_mem ha hb,by rw [add_pow_char_pow,hax,hby]⟩
  | mul x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      exact ⟨a*b,(perfectOrderAt A D L p n).mul_mem ha hb,by rw [mul_pow,hax,hby]⟩

omit [IsDomain D] in
lemma root_conductor (g : A)
    (hg : ∀ c : PerfectClosure L p, IsIntegral (PerfectClosure A p) c →
      PerfectClosure.of A p g • c ∈ perfectOrder A D L p)
    (n : ℕ) (c : PerfectClosure L p) (hc : IsIntegral (PerfectClosure A p) c) :
    rootMap A p n g • c ∈ perfectOrderAt A D L p n := by
  obtain ⟨y,hy,heq⟩ := perfectOrder_roots A D L p n (hg (c^(p^n)) (hc.pow _))
  have hh : y = rootMap A p n g • c := by
    apply (injective_frobenius (PerfectClosure L p) p).iterate n
    rw [iterate_frobenius,iterate_frobenius,heq,smul_pow,rootMap_pow]
  rwa [hh] at hy

end Lech.TraceConductor

open scoped TensorProduct nonZeroDivisors
namespace Lech.TensorInjection

lemma injective_of_basis {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (b : Module.Basis ι R M) (f : M →ₗ[R] N)
    (h : LinearIndependent R (fun i => f (b i))) : Function.Injective f := by
  have he : f = b.constr R (fun i => f (b i)) := by
    apply b.ext
    intro i
    simp
  rw [he]
  exact b.injective_constr_of_linearIndependent h

section Field
variable {K L Q E : Type*} [Field K] [Field L] [Field Q] [CommRing E]
  [Algebra K L] [Algebra K Q] [Algebra K E] [Algebra Q E]
  [IsScalarTower K Q E]

lemma field_product_injective {ι : Type*} (b : Module.Basis ι K L) (f : L →ₐ[K] E)
    (h : LinearIndependent Q (fun i => f (b i))) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f) := by
  apply injective_of_basis (b.baseChange Q)
    (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f).toLinearMap
  simpa only [AlgHom.toLinearMap_apply, Module.Basis.baseChange_apply,Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul,
    map_one,one_mul] using h
end Field

section IntegralBase
variable {A K P Q : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing P] [Field Q] [Algebra A P] [Algebra A Q]
  [Algebra K Q] [IsScalarTower A K Q]

omit [IsDomain A] in
 
lemma localized_product_injective (f : P →ₐ[A] Q) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f) := by
  let : Algebra P (K ⊗[A] P) := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid P A⁰
  let F := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f
  apply IsLocalization.injective_of_map_algebraMap_zero (M := S) (K ⊗[A] P) F.toRingHom
  intro x hx
  change F (1 ⊗ₜ[A] x) = 0 at hx
  have hx' : f x = 0 := by
    simpa [F,Algebra.TensorProduct.productLeftAlgHom,Algebra.TensorProduct.lift_tmul] using hx
  have he : x = 0 := (map_eq_zero_iff _ hf).mp hx'
  simp [he]
end IntegralBase

variable {A K D L P Q E : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing D] [Algebra A D] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L]
  [CommRing P] [Algebra A P] [Module.Flat A P]
  [Field Q] [Algebra A Q] [Algebra K Q] [IsScalarTower A K Q]
  [CommRing E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
  [Algebra Q E] [IsScalarTower K Q E] [IsScalarTower A Q E]

omit [IsDomain A] in
 

theorem stage_product_injective {ι : Type*} (b : Module.Basis ι K L)
    (fD : D →ₐ[A] L) (hfD : Function.Injective fD)
    (fP : P →ₐ[A] Q) (hfP : Function.Injective fP)
    (fL : L →ₐ[K] E) (hind : LinearIndependent Q (fun i => fL (b i))) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD)) := by
  let U := K ⊗[A] P
  let j : U →ₐ[K] Q := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) fP
  have hj : Function.Injective j := localized_product_injective fP hfP
  let k : L ⊗[K] U →ₐ[K] L ⊗[K] Q :=
    Algebra.TensorProduct.map (AlgHom.id K L) j
  have hk : Function.Injective k := by
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := L) j.toLinearMap hj
  let e := Algebra.TensorProduct.cancelBaseChange A K K L P
  let v : D ⊗[A] P →ₐ[A] L ⊗[A] P :=
    Algebra.TensorProduct.map fD (AlgHom.id A P)
  have hv : Function.Injective v :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := P) fD.toLinearMap hfD
  let t := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) fL
  have ht : Function.Injective t := field_product_injective b fL hind
  let F : P ⊗[A] D →ₐ[A] E := (t.restrictScalars A).comp
    (((Algebra.TensorProduct.comm K L Q).toAlgHom.restrictScalars A).comp
      ((k.restrictScalars A).comp ((e.symm.toAlgHom.restrictScalars A).comp
        (v.comp (Algebra.TensorProduct.comm A P D).toAlgHom))))
  have hF : Function.Injective F := ht.comp
    ((Algebra.TensorProduct.comm K L Q).injective.comp
      (hk.comp (e.symm.injective.comp (hv.comp (Algebra.TensorProduct.comm A P D).injective))))
  have heq : F = Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD) := by
    apply Algebra.TensorProduct.ext'
    intro a d
    simp [F,v,k,j,t,e,Algebra.TensorProduct.productMap,
      Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul, mul_comm]
    change fL (fD d) * (algebraMap Q E) ((algebraMap K Q) 1 * fP a) = _
    simp
  rwa [heq] at hF
end Lech.TensorInjection


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

lemma rootMap_eq_frobeniusEquiv (n : ℕ) : rootMap A p n =
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.toRingHom.comp
      (PerfectClosure.of A p) := by
  ext a
  apply (iterateFrobeniusEquiv (PerfectClosure A p) p n).injective
  change (rootMap A p n a)^(p^n) = _
  rw [rootMap_pow]
  exact ((iterateFrobeniusEquiv (PerfectClosure A p) p n).apply_symm_apply _).symm

lemma rootMap_flat (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    (rootMap A p n).Flat := by
  rw [rootMap_eq_frobeniusEquiv]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.bijective)

end Lech.RootTower


namespace Lech.RootTower
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

 
lemma root_basis_independent [Algebra.IsSeparable K L] {ι : Type*}
    (b : Module.Basis ι K L) (n : ℕ) :
    LinearIndependent (PerfectClosure K p) (fun i => rootMap L p n (b i)) := by
  let : Algebra K (PerfectClosure K p) := (rootMap K p n).toAlgebra
  let : Algebra K (PerfectClosure L p) := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K (PerfectClosure K p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (perfectMap_root p (algebraMap K L) n a).symm)
  let f : L →ₐ[K] PerfectClosure L p :=
    { __ := rootMap L p n, commutes' _ := rfl }
  let : IsPurelyInseparable K (PerfectClosure K p) :=
    (isPurelyInseparable_iff_pow_mem K p).mpr (by
      intro x
      obtain ⟨j,a,ha⟩ := IsPRadical.pow_mem (PerfectClosure.of K p) p x
      refine ⟨j, a^(p^n), ?_⟩
      change rootMap K p n (a^(p^n)) = x^(p^j)
      rw [map_pow,rootMap_pow]
      exact ha)
  apply LinearIndependent.map_of_isPurelyInseparable_of_isSeparable (F := K)
  · intro i
    exact (Algebra.IsSeparable.isSeparable K (b i)).map f (rootMap_injective L p n)
  · exact b.linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr (rootMap_injective L p n))

end Lech.RootTower


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p] [CharP L p]

omit [IsDomain A] [IsDomain D] [Algebra A D] [IsScalarTower A D L] [CharP D p] in
 
lemma stages_mono : Monotone (perfectOrderAt A D L p) := by
  intro n m h
  apply Algebra.adjoin_le
  rintro _ ⟨d,rfl⟩
  have hd : rootMap L p m (algebraMap D L (d^(p^(m-n)))) =
      rootMap L p n (algebraMap D L d) := by
    rw [map_pow]
    exact rootMap_transition L p n m h (algebraMap D L d)
  change rootMap L p n (algebraMap D L d) ∈ _
  rw [← hd]
  exact Algebra.subset_adjoin ⟨d^(p^(m-n)),rfl⟩

omit [IsDomain A] [Algebra A D] [IsScalarTower A D L] in
lemma embedded_perfection_mem (c : PerfectClosure D p) :
    ∃ n, perfectMap p (algebraMap D L) c ∈ perfectOrderAt A D L p n := by
  obtain ⟨⟨n,d⟩,rfl⟩ := PerfectClosure.mk_surjective D p c
  refine ⟨n,?_⟩
  change perfectMap p (algebraMap D L) (rootMap D p n d) ∈ _
  rw [perfectMap_root]
  exact Algebra.subset_adjoin ⟨d,rfl⟩

omit [IsDomain A] in
 
lemma embedded_perfection_integral [Algebra.IsIntegral A D] (c : PerfectClosure D p) :
    IsIntegral (PerfectClosure A p) (perfectMap p (algebraMap D L) c) := by
  let : Algebra A (PerfectClosure L p) :=
    ((PerfectClosure.of L p).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm
  let f : D →ₐ[A] PerfectClosure L p :=
    { __ := (PerfectClosure.of L p).comp (algebraMap D L)
      commutes' a := congrArg (PerfectClosure.of L p) (IsScalarTower.algebraMap_apply A D L a).symm }
  obtain ⟨⟨n,d⟩,rfl⟩ := PerfectClosure.mk_surjective D p c
  change IsIntegral (PerfectClosure A p)
    (perfectMap p (algebraMap D L) (rootMap D p n d))
  rw [perfectMap_root]
  apply IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n)
  rw [rootMap_pow]
  exact (IsIntegral.map f (Algebra.IsIntegral.isIntegral (R := A) d)).tower_top

end Lech.PerfectStages


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
def tensorStageMap (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] PerfectClosure L p := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  let : Algebra A (PerfectClosure L p) :=
    ((rootMap L p n).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (perfectMap_root p (algebraMap A L) n a).symm)
  let f : D →ₐ[A] PerfectClosure L p :=
    { __ := (rootMap L p n).comp (algebraMap D L)
      commutes' a := congrArg (rootMap L p n) (IsScalarTower.algebraMap_apply A D L a).symm }
  exact Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (PerfectClosure A p) _) f

omit [IsDomain D] in
lemma tensorStageMap_apply (n : ℕ) (a : PerfectClosure A p) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorStageMap A D L p n (a ⊗ₜ[A] d) =
      perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) := rfl

end Lech.PerfectStages


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP K p] [CharP L p]

include K in
omit [IsDomain D] in
 
theorem tensorStageMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorStageMap A D L p n) := by
  let P := PerfectClosure A p
  let Q := PerfectClosure K p
  let E := PerfectClosure L p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Module.Flat A P := rootMap_flat A p hflat n
  let : Algebra K Q := (rootMap K p n).toAlgebra
  let : Algebra A Q := ((rootMap K p n).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K E := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : Algebra A E := ((rootMap L p n).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact congrArg (rootMap L p n) (IsScalarTower.algebraMap_apply A K L a))
  let : IsScalarTower K Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (perfectMap_root p (algebraMap K L) n a).symm)
  let : IsScalarTower A Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change rootMap L p n (algebraMap A L a) =
      perfectMap p (algebraMap K L) (rootMap K p n (algebraMap A K a))
    rw [perfectMap_root,IsScalarTower.algebraMap_apply A K L])
  let fP : P →ₐ[A] Q :=
    { __ := perfectMap p (algebraMap A K)
      commutes' a := perfectMap_root p (algebraMap A K) n a }
  let fL : L →ₐ[K] E := { __ := rootMap L p n, commutes' _ := rfl }
  have hh := Lech.TensorInjection.stage_product_injective (Module.Free.chooseBasis K L)
    (IsScalarTower.toAlgHom A D L) (IsFractionRing.injective D L)
    fP (perfectMap_injective p _ (IsFractionRing.injective A K)) fL
    (root_basis_independent K L p (Module.Free.chooseBasis K L) n)
  have he : (tensorStageMap A D L p n).toRingHom =
      (Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom A Q E).comp fP)
        ((fL.restrictScalars A).comp (IsScalarTower.toAlgHom A D L))).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a d =>
        change perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) =
          perfectMap p (algebraMap K L) (perfectMap p (algebraMap A K) a) *
            rootMap L p n (algebraMap D L d)
        congr 1
        have hp := congrArg (fun f : PerfectClosure A p →+* PerfectClosure L p => f a)
          (perfectMap_comp p (algebraMap A K) (algebraMap K L))
        simpa only [RingHom.comp_apply,← IsScalarTower.algebraMap_eq] using hp.symm
    | add x y hx hy => simp only [map_add,hx,hy]
  change Function.Injective (tensorStageMap A D L p n).toRingHom
  rw [he]
  exact hh

end Lech.PerfectStages


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [Field L]
  [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
lemma tensorStageMap_range (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (tensorStageMap A D L p n).range = perfectOrderAt A D L p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul a d =>
        change perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) ∈ _
        exact (perfectOrderAt A D L p n).mul_mem
          ((perfectOrderAt A D L p n).algebraMap_mem a) (Algebra.subset_adjoin ⟨d,rfl⟩)
    | add x y hx hy => simpa only [map_add] using (perfectOrderAt A D L p n).add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨d,rfl⟩
    refine ⟨1 ⊗ₜ[A] d,?_⟩
    change perfectMap p (algebraMap A L) 1 * rootMap L p n (algebraMap D L d) = _
    simp

end Lech.PerfectStages


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

instance domainAlgebra : Algebra (PerfectClosure A p) (PerfectClosure D p) :=
  (perfectMap p (algebraMap A D)).toAlgebra

def stage (n : ℕ) : Subalgebra (PerfectClosure A p) (PerfectClosure D p) :=
  Algebra.adjoin (PerfectClosure A p) (Set.range (rootMap D p n))

def tensorMap (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] PerfectClosure D p := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  let : Algebra A (PerfectClosure D p) := ((rootMap D p n).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure D p) :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (perfectMap_root p _ n a).symm)
  let f : D →ₐ[A] PerfectClosure D p := { __ := rootMap D p n, commutes' _ := rfl }
  exact Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (PerfectClosure A p) _) f

lemma tensorMap_apply (n : ℕ) (a : PerfectClosure A p) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorMap A D p n (a ⊗ₜ[A] d) = perfectMap p (algebraMap A D) a * rootMap D p n d := rfl

lemma tensorMap_range (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (tensorMap A D p n).range = stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul a d =>
      change perfectMap p (algebraMap A D) a * rootMap D p n d ∈ _
      exact (stage A D p n).mul_mem ((stage A D p n).algebraMap_mem a)
        (Algebra.subset_adjoin ⟨d,rfl⟩)
    | add x y hx hy => simpa only [map_add] using (stage A D p n).add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨d,rfl⟩
    refine ⟨1 ⊗ₜ[A] d,?_⟩
    change tensorMap A D p n (1 ⊗ₜ[A] d) = _
    rw [tensorMap_apply,map_one,one_mul]

omit [IsDomain A] in
lemma stage_mono : Monotone (stage A D p) := by
  intro n m h
  apply Algebra.adjoin_le
  rintro _ ⟨d,rfl⟩
  rw [← rootMap_transition D p n m h d]
  exact Algebra.subset_adjoin ⟨iterateFrobenius D p (m-n) d,rfl⟩

omit [IsDomain A] in
lemma stage_exhaustive (c : PerfectClosure D p) : ∃ n, c ∈ stage A D p n := by
  obtain ⟨⟨n,d⟩,rfl⟩ := PerfectClosure.mk_surjective D p c
  exact ⟨n,Algebra.subset_adjoin ⟨d,rfl⟩⟩

variable (L : Type*) [Field L] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  [CharP L p]

def fieldMap : PerfectClosure D p →ₐ[PerfectClosure A p] PerfectClosure L p where
  __ := perfectMap p (algebraMap D L)
  commutes' a := by
    change perfectMap p (algebraMap D L) (perfectMap p (algebraMap A D) a) = _
    rw [← RingHom.comp_apply,perfectMap_comp,← IsScalarTower.algebraMap_eq]
    rfl

lemma fieldMap_tensor (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (fieldMap A D p L).comp (tensorMap A D p n) =
      Lech.PerfectStages.tensorStageMap A D L p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a d =>
    change perfectMap p (algebraMap D L)
      (perfectMap p (algebraMap A D) a * rootMap D p n d) = _
    rw [map_mul,perfectMap_root]
    change _ = perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d)
    congr 1
    rw [← RingHom.comp_apply,perfectMap_comp,← IsScalarTower.algebraMap_eq]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [IsScalarTower A K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p]

include L K in
omit [FiniteDimensional K L] in
lemma tensorMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorMap A D p n) := by
  have h := Lech.PerfectStages.tensorStageMap_injective A D K L p hflat n
  have hh := fieldMap_tensor A D p L n
  intro x y hxy
  apply h
  rw [← hh]
  exact congrArg (fieldMap A D p L) hxy

include L K in
 

theorem exists_conductor [IsIntegrallyClosed A] [Algebra.IsIntegral A D] :
    ∃ g : A, g ≠ 0 ∧ ∀ (n : ℕ) (c : PerfectClosure D p),
      rootMap A p n g • c ∈ stage A D p n := by
  obtain ⟨g,hg,hgc⟩ := Lech.TraceConductor.exists_perfect_conductor A D K L p
  refine ⟨g,hg,fun n c => ?_⟩
  have hi := Lech.PerfectStages.embedded_perfection_integral A D L p c
  have hc := Lech.TraceConductor.root_conductor A D L p g hgc n _ hi
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  rw [← Lech.PerfectStages.tensorStageMap_range A D L p n] at hc
  obtain ⟨x,hx⟩ := hc
  rw [← tensorMap_range A D p n]
  refine ⟨x,?_⟩
  apply perfectMap_injective p (algebraMap D L) (IsFractionRing.injective D L)
  change (fieldMap A D p L) (tensorMap A D p n x) =
    (fieldMap A D p L) (rootMap A p n g • c)
  rw [map_smul,← AlgHom.comp_apply, fieldMap_tensor]
  exact hx

end Lech.PerfectDomainStages
end

end OAI
