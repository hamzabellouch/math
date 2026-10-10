import Mathlib
import OAI.RingTheory.Multiplicity.PerfectDomainStagesTensorTo

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech

 

theorem finite_free_factorization (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (g : A), g ≠ 0 ∧
      ∃ (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A)),
        u.comp v = g • LinearMap.id ∧ v.comp u = g • LinearMap.id := by
  let := Module.finitePresentation_of_finite A M
  let K := FractionRing A
  let MK := LocalizedModule A⁰ M
  let f : M →ₗ[A] MK := LocalizedModule.mkLinearMap A⁰ M
  let n := Module.finrank K MK
  let e : MK ≃ₗ[A] (Fin n → K) := (Module.finBasis K MK).equivFun.restrictScalars A
  let j : (Fin n → A) →ₗ[A] (Fin n → K) :=
    LinearMap.pi fun i => (Algebra.linearMap A K).comp (LinearMap.proj i)
  have : IsLocalizedModule A⁰ j := by dsimp [j]; infer_instance
  obtain ⟨v,s,hv⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ j
    (e.toLinearMap.comp f)
  obtain ⟨u,t,hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ f
    (e.symm.toLinearMap.comp j)
  have huv : f.comp (u.comp v) = f.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu (v x)
    have hs := LinearMap.congr_fun hv x
    change f (u (v x)) = (t:A) • e.symm (j (v x)) at ht
    change j (v x) = (s:A) • e (f x) at hs
    change f (u (v x)) = f (((t:A)*(s:A)) • x)
    rw [ht,hs,map_smul,e.symm_apply_apply,map_smul,mul_smul]
  have hvu : j.comp (v.comp u) = j.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu x
    have hs := LinearMap.congr_fun hv (u x)
    change f (u x) = (t:A) • e.symm (j x) at ht
    change j (v (u x)) = (s:A) • e (f (u x)) at hs
    change j (v (u x)) = j (((t:A)*(s:A)) • x)
    rw [hs,ht,map_smul,e.apply_symm_apply,map_smul,mul_smul,smul_comm]
  obtain ⟨a,ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ f
    (u.comp v) (((t:A)*(s:A)) • LinearMap.id) huv
  obtain ⟨b,hb⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ j
    (v.comp u) (((t:A)*(s:A)) • LinearMap.id) hvu
  refine ⟨n,(a:A)*(b:A)*((t:A)*(s:A)),?_, ((a:A)*(b:A)) • u,v,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero a)
      (nonZeroDivisors.coe_ne_zero b))
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero t) (nonZeroDivisors.coe_ne_zero s))
  · rw [LinearMap.smul_comp, mul_comm (a:A) (b:A),mul_smul]
    change (b:A) • ((a:A) • u.comp v) = _
    rw [show (a:A) • u.comp v = (a:A) • (((t:A)*(s:A)) • LinearMap.id) from ha]
    simp only [smul_smul]
    congr 1
    ring
  · rw [LinearMap.comp_smul,mul_smul]
    change (a:A) • ((b:A) • v.comp u) = _
    rw [show (b:A) • v.comp u = (b:A) • (((t:A)*(s:A)) • LinearMap.id) from hb]
    simp only [smul_smul]
    congr 1
    ring

variable {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[A] M) (hM : Module.length A M ≠ ⊤) :
    Module.length A f.ker = Module.length A (M ⧸ f.range) := by
  have h₁ := Module.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := Module.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : Module.length A f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact WithTop.add_left_cancel hr ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[A] M) (q : N →ₗ[A] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : A) (hg : ∀ x : P, g • x = 0) (hM : Module.length A M ≠ ⊤) :
    Module.length A P ≤ Module.length A (M ⧸ (LinearMap.lsmul A M g).range) := by
  let fN := LinearMap.lsmul A N g
  let fM := LinearMap.lsmul A M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[A] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : Module.length A N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective i hi)
  calc
    Module.length A P ≤ Module.length A (N ⧸ fN.range) :=
      Module.length_le_of_surjective q' hq'
    _ = Module.length A fN.ker := (length_kernel_eq_cokernel fN hN).symm
    _ ≤ Module.length A fM.ker := Module.length_le_of_injective i' hi'
    _ = _ := length_kernel_eq_cokernel fM hM

lemma length_scalar_cokernel_pi (g : A) (n : ℕ) :
    Module.length A ((Fin n → A) ⧸ (LinearMap.lsmul A (Fin n → A) g).range) =
      n * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) := by
  classical
  have he : (LinearMap.lsmul A (Fin n → A) g).range =
      Submodule.pi Set.univ (fun _ : Fin n => (LinearMap.lsmul A A g).range) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩ i _
      exact ⟨y i,rfl⟩
    · intro hx
      have hx' : ∀ i, ∃ y : A, g • y = x i := fun i => hx i (Set.mem_univ i)
      choose y hy using hx'
      exact ⟨y,funext hy⟩
  rw [(Submodule.quotEquivOfEq _ _ he).length_eq,
    (Submodule.quotientPi (fun _ : Fin n => (LinearMap.lsmul A A g).range)).length_eq,
    Module.length_pi_of_fintype]
  simp

 

lemma length_isogeny (n c : ℕ) (g : A)
    (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A))
    (huv : u.comp v = g • LinearMap.id)
    (hvu : v.comp u = g • LinearMap.id)
    (w : (Fin c → A) →ₗ[A] M) (hw : Function.Surjective w)
    (hA : Module.length A A ≠ ⊤) :
    Module.length A M ≤ n * Module.length A A +
        c * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) ∧
    n * Module.length A A ≤ Module.length A M +
        n * Module.length A (A ⧸ (LinearMap.lsmul A A g).range) := by
  have hfree (d : ℕ) : Module.length A (Fin d → A) = d * Module.length A A := by
    simp
  have hfin (d : ℕ) : Module.length A (Fin d → A) ≠ ⊤ := by
    rw [hfree]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top d) hA
  have hker : ∀ x : u.ker, g • x = 0 := by
    intro x
    apply Subtype.ext
    have hh := LinearMap.congr_fun hvu x
    simpa using hh.symm
  have hcoker : ∀ x : M ⧸ u.range, g • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change u.range.mkQ (g • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨v x,LinearMap.congr_fun huv x⟩
  have hk := length_torsion_subquotient_le u.ker.subtype LinearMap.id
    (Submodule.subtype_injective _) Function.surjective_id g hker (hfin n)
  rw [length_scalar_cokernel_pi] at hk
  let wc := u.range.mkQ.comp w
  have hwc : Function.Surjective wc := u.range.mkQ_surjective.comp hw
  have hc := length_torsion_subquotient_le LinearMap.id wc
    Function.injective_id hwc g hcoker (hfin c)
  rw [length_scalar_cokernel_pi] at hc
  have hr := Module.length_le_of_surjective u.rangeRestrict u.surjective_rangeRestrict
  have hr' := Module.length_le_of_injective u.range.subtype (Submodule.subtype_injective _)
  have hcod := Module.length_eq_add_of_exact u.range.subtype u.range.mkQ
    (Submodule.subtype_injective _) u.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ u.range)
  have hdom := Module.length_eq_add_of_exact u.rangeRestrict.ker.subtype u.rangeRestrict
    (Submodule.subtype_injective _) u.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map u.rangeRestrict)
  have hkr : u.rangeRestrict.ker = u.ker := by ext x; simp
  rw [hkr,hfree] at hdom
  constructor
  · rw [hcod]
    exact add_le_add (by simpa only [hfree] using hr) hc
  · rw [hdom,add_comm]
    exact add_le_add hr' hk

lemma scalar_range (a : A) : (LinearMap.lsmul A A a).range = Ideal.span {a} := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, smul_eq_mul,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨y,hy⟩ => ⟨y,by simpa [mul_comm] using hy.symm⟩,
    fun ⟨y,hy⟩ => ⟨y,by simpa [mul_comm] using hy.symm⟩⟩

lemma scalar_cokernel_quotient_length (I : Ideal A) (g : A) :
    Module.length (A ⧸ I)
      ((A ⧸ I) ⧸ (LinearMap.lsmul (A ⧸ I) (A ⧸ I) (Ideal.Quotient.mk I g)).range) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  rw [scalar_range]
  have hm : Ideal.span {Ideal.Quotient.mk I g} =
      (Ideal.span {g}).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hm, ← Module.length_eq_of_surjective (R := A ⧸ I)
    (Ideal.Quotient.mk_surjective)]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A I (Ideal.span {g})).toLinearEquiv.length_eq

lemma baseChange_isogeny {B : Type*} [CommRing B] [Algebra A B]
    (n : ℕ) (g : A) (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A))
    (huv : u.comp v = g • LinearMap.id) (hvu : v.comp u = g • LinearMap.id) :
    ∃ (u' : (Fin n → B) →ₗ[B] B ⊗[A] M) (v' : B ⊗[A] M →ₗ[B] (Fin n → B)),
      u'.comp v' = (algebraMap A B g) • LinearMap.id ∧
      v'.comp u' = (algebraMap A B g) • LinearMap.id := by
  let e := TensorProduct.piScalarRight A B B (Fin n)
  refine ⟨(u.baseChange B).comp e.symm.toLinearMap,
    e.toLinearMap.comp (v.baseChange B),?_,?_⟩
  · apply LinearMap.ext
    intro x
    change u.baseChange B (e.symm (e (v.baseChange B x))) = _
    rw [e.symm_apply_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      huv, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    simp [Algebra.smul_def]
  · apply LinearMap.ext
    intro x
    change e (v.baseChange B (u.baseChange B (e.symm x))) = _
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      hvu, LinearMap.baseChange_smul, LinearMap.baseChange_id]
    change e (g • e.symm x) = (algebraMap A B g) • x
    rw [← IsScalarTower.algebraMap_smul B g (e.symm x), map_smul, e.apply_symm_apply]

 

theorem finite_module_colength_compare (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n c : ℕ) (g : A), g ≠ 0 ∧ ∀ (I : Ideal A),
      Module.length A (A ⧸ I) ≠ ⊤ →
      Module.length A (M ⧸ (I • (⊤ : Submodule A M))) ≤
        n * Module.length A (A ⧸ I) + c * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ∧
      n * Module.length A (A ⧸ I) ≤
        Module.length A (M ⧸ (I • (⊤ : Submodule A M))) +
        n * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  obtain ⟨n,g,hg,u,v,huv,hvu⟩ := finite_free_factorization A M
  obtain ⟨c,w,hw⟩ := Module.Finite.exists_fin' A M
  refine ⟨n,c,g,hg,fun I hI => ?_⟩
  let B := A ⧸ I
  obtain ⟨u',v',huv',hvu'⟩ := baseChange_isogeny (B := B) n g u v huv hvu
  let e := TensorProduct.piScalarRight A B B (Fin c)
  let w' := (w.baseChange B).comp e.symm.toLinearMap
  have hw' : Function.Surjective w' := (LinearMap.baseChange_surjective B hw).comp e.symm.surjective
  have hB : Module.length B B ≠ ⊤ := by
    rwa [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
  have h := length_isogeny n c (algebraMap A B g) u' v' huv' hvu' w' hw' hB
  have hlen : Module.length B (B ⊗[A] M) = Module.length A (M ⧸ I • (⊤ : Submodule A M)) := by
    rw [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
    exact (TensorProduct.quotTensorEquivQuotSMul M I).length_eq
  have hscalar : Module.length B
      (B ⧸ (LinearMap.lsmul B B (algebraMap A B g)).range) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {g})) :=
    scalar_cokernel_quotient_length I g
  rw [hlen, hscalar, ← Module.length_eq_of_surjective (R := B)
    Ideal.Quotient.mk_surjective] at h
  exact h

 

theorem finite_module_colength_error (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n c : ℕ) (g : A), g ≠ 0 ∧ ∀ I : Ideal A,
      Module.length A (A ⧸ I) ≠ ⊤ →
      |((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) -
        (n : ℝ) * ((Module.length A (A ⧸ I)).toNat : ℝ)| ≤
        (c : ℝ) * ((Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat : ℝ) := by
  obtain ⟨n,c,g,hg,h⟩ := finite_module_colength_compare A M
  refine ⟨n,c+n,g,hg,fun I hI => ?_⟩
  obtain ⟨h₁,h₂⟩ := h I hI
  have hG : Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hI
    let f := I.mapQ (I ⊔ Ideal.span {g}) LinearMap.id le_sup_left
    apply Module.length_le_of_surjective f
    intro x
    obtain ⟨a,rfl⟩ := (I ⊔ Ideal.span {g}).mkQ_surjective x
    exact ⟨I.mkQ a,rfl⟩
  have hM : Module.length A (M ⧸ I • (⊤ : Submodule A M)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ h₁
    exact WithTop.add_ne_top.mpr ⟨WithTop.mul_ne_top (ENat.natCast_ne_top _) hI,
      WithTop.mul_ne_top (ENat.natCast_ne_top _) hG⟩
  rw [← ENat.natCast_toNat hM, ← ENat.natCast_toNat hI,
    ← ENat.natCast_toNat hG] at h₁ h₂
  have hr₁ : ((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) ≤
      (n : ℝ) * (Module.length A (A ⧸ I)).toNat +
      (c : ℝ) * (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by
    exact_mod_cast h₁
  have hr₂ : (n : ℝ) * (Module.length A (A ⧸ I)).toNat ≤
      ((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) +
      (n : ℝ) * (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by
    exact_mod_cast h₂
  have hgn : (0 : ℝ) ≤ (Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat := by positivity
  have hcn : (0 : ℝ) ≤ c := by positivity
  have hnn : (0 : ℝ) ≤ n := by positivity
  rw [Nat.cast_add,abs_le]
  constructor <;> nlinarith

end Lech


namespace Lech
open Filter
open scoped Topology

lemma tendsto_of_abs_sub_le {f g ε : ℕ → ℝ} {a : ℝ}
    (hg : Tendsto g atTop (𝓝 a)) (he : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, |f n - g n| ≤ ε n) : Tendsto f atTop (𝓝 a) := by
  have hz : Tendsto (fun n => |f n - g n|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) h he
  have hs : Tendsto (fun n => f n - g n) atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [Real.dist_eq,sub_zero] using hz
  simpa only [sub_add_cancel,zero_add] using hs.add hg

 

theorem finite_module_asymptotic (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ n : ℕ, ∀ (I : ℕ → Ideal A) (u : ℕ → ℝ) (a : ℝ),
      (∀ᶠ q in atTop, Module.length A (A ⧸ I q) ≠ ⊤) →
      (∀ᶠ q in atTop, 0 < u q) →
      Tendsto (fun q => ((Module.length A (A ⧸ I q)).toNat : ℝ) / u q) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        ((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q) atTop (𝓝 0)) →
      Tendsto (fun q => ((Module.length A (M ⧸ I q • (⊤ : Submodule A M))).toNat : ℝ) / u q)
        atTop (𝓝 ((n : ℝ) * a)) := by
  obtain ⟨n,c,g,hg,h⟩ := finite_module_colength_error A M
  refine ⟨n,fun I u a hI hu hA hG => ?_⟩
  apply tendsto_of_abs_sub_le (hA.const_mul (n : ℝ))
    (show Tendsto (fun q => (c : ℝ) *
      (((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q)) atTop (𝓝 0) from by
        simpa using (hG g hg).const_mul (c : ℝ))
  filter_upwards [hI,hu] with q hI hu
  have hh := div_le_div_of_nonneg_right (h (I q) hI) hu.le
  simpa only [← mul_div_assoc,← sub_div,abs_div,abs_of_pos hu] using hh

end Lech


namespace Lech
open scoped TensorProduct
theorem finite_module_colength_compare_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ (n c : ℕ) (g : A), 0 < n ∧ g ≠ 0 ∧ ∀ (I : Ideal A),
      Module.length A (A ⧸ I) ≠ ⊤ →
      Module.length A (M ⧸ (I • (⊤ : Submodule A M))) ≤
        n * Module.length A (A ⧸ I) + c * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ∧
      n * Module.length A (A ⧸ I) ≤
        Module.length A (M ⧸ (I • (⊤ : Submodule A M))) +
        n * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  obtain ⟨n,g,hg,u,v,huv,hvu⟩ := finite_free_factorization A M
  obtain ⟨c,w,hw⟩ := Module.Finite.exists_fin' A M
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    apply hfaithful g hg
    rw [← huv]
    ext x
    change u (v x) = 0
    rw [Subsingleton.elim (v x) 0,map_zero]
  refine ⟨n,c,g,hn,hg,fun I hI => ?_⟩
  let B := A ⧸ I
  obtain ⟨u',v',huv',hvu'⟩ := baseChange_isogeny (B := B) n g u v huv hvu
  let e := TensorProduct.piScalarRight A B B (Fin c)
  let w' := (w.baseChange B).comp e.symm.toLinearMap
  have hw' : Function.Surjective w' := (LinearMap.baseChange_surjective B hw).comp e.symm.surjective
  have hB : Module.length B B ≠ ⊤ := by
    rwa [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
  have h := length_isogeny n c (algebraMap A B g) u' v' huv' hvu' w' hw' hB
  have hlen : Module.length B (B ⊗[A] M) = Module.length A (M ⧸ I • (⊤ : Submodule A M)) := by
    rw [← Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
    exact (TensorProduct.quotTensorEquivQuotSMul M I).length_eq
  have hscalar : Module.length B
      (B ⧸ (LinearMap.lsmul B B (algebraMap A B g)).range) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {g})) :=
    scalar_cokernel_quotient_length I g
  rw [hlen, hscalar, ← Module.length_eq_of_surjective (R := B)
    Ideal.Quotient.mk_surjective] at h
  exact h

end Lech


namespace Lech
open Filter
open scoped ENNReal Topology
 

theorem finite_module_asymptoticENN (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ (I : ℕ → Ideal A) (w : ℕ → ℝ≥0∞) (a : ℝ≥0∞),
      (∀ᶠ q in atTop, Module.length A (A ⧸ I q) ≠ ⊤) →
      Tendsto (fun q => w q * (Module.length A (A ⧸ I q)).toENNReal) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        w q * (Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toENNReal) atTop (𝓝 0)) →
      Tendsto (fun q => w q * (Module.length A (M ⧸ I q • (⊤ : Submodule A M))).toENNReal)
        atTop (𝓝 ((n : ℝ≥0∞) * a)) := by
  obtain ⟨n,c,g,hn,hg,h⟩ := finite_module_colength_compare_pos A M hfaithful
  refine ⟨n,hn,fun I w a hI hA hG => ?_⟩
  have hb := ENNReal.Tendsto.const_mul (a := (n : ℝ≥0∞)) hA (Or.inr (by simp))
  have hec := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) (hG g hg) (Or.inr (by simp))
  have hen := ENNReal.Tendsto.const_mul (a := (n : ℝ≥0∞)) (hG g hg) (Or.inr (by simp))
  simp only [mul_zero] at hec hen
  have hu := hb.add hec
  have hl := (ENNReal.tendsto_sub (a := (n : ℝ≥0∞)*a) (b := 0) (Or.inr (by simp))).comp
    (hb.prodMk_nhds hen)
  simp only [add_zero,tsub_zero] at hu hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hI] with q hI
    obtain ⟨_,h₂⟩ := h (I q) hI
    have hh := mul_le_mul_right (ENat.toENNReal_mono h₂) (w q)
    simp only [ENat.toENNReal_add,ENat.toENNReal_mul,ENat.toENNReal_coe,
      mul_add,← mul_assoc] at hh
    rw [mul_comm (w q) (n : ℝ≥0∞)] at hh
    apply tsub_le_iff_right.mpr
    simpa only [Function.comp_apply, mul_assoc] using hh
  · filter_upwards [hI] with q hI
    obtain ⟨h₁,_⟩ := h (I q) hI
    have hh := mul_le_mul_right (ENat.toENNReal_mono h₁) (w q)
    simpa only [ENat.toENNReal_add,ENat.toENNReal_mul,ENat.toENNReal_coe,
      mul_add,mul_assoc,mul_left_comm] using hh
end Lech
end
end

end OAI
