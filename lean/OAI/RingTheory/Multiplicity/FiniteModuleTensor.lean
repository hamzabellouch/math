import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusModule
import OAI.RingTheory.Multiplicity.LechFiniteFree

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech
variable {A : Type*} [CommRing A]

lemma length_scalar_cokernel_pi_module {N : Type*} [AddCommGroup N] [Module A N]
    (g : A) (n : ℕ) :
    Module.length A ((Fin n → N) ⧸ (LinearMap.lsmul A (Fin n → N) g).range) =
      n * Module.length A (N ⧸ (LinearMap.lsmul A N g).range) := by
  classical
  have he : (LinearMap.lsmul A (Fin n → N) g).range =
      Submodule.pi Set.univ (fun _ : Fin n => (LinearMap.lsmul A N g).range) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩ i _
      exact ⟨y i,rfl⟩
    · intro hx
      have hx' : ∀ i, ∃ y : N, g • y = x i := fun i => hx i (Set.mem_univ i)
      choose y hy using hx'
      exact ⟨y,funext hy⟩
  rw [(Submodule.quotEquivOfEq _ _ he).length_eq,
    (Submodule.quotientPi (fun _ : Fin n => (LinearMap.lsmul A N g).range)).length_eq,
    Module.length_pi_of_fintype]
  simp

lemma length_module_isogeny {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (n c : ℕ) (g : A)
    (u : (Fin n → N) →ₗ[A] P) (v : P →ₗ[A] (Fin n → N))
    (huv : u.comp v = g • LinearMap.id) (hvu : v.comp u = g • LinearMap.id)
    (w : (Fin c → N) →ₗ[A] P) (hw : Function.Surjective w)
    (hN : Module.length A N ≠ ⊤) :
    Module.length A P ≤ n * Module.length A N +
        c * Module.length A (N ⧸ (LinearMap.lsmul A N g).range) ∧
    n * Module.length A N ≤ Module.length A P +
        n * Module.length A (N ⧸ (LinearMap.lsmul A N g).range) := by
  have hfree (d : ℕ) : Module.length A (Fin d → N) = d * Module.length A N := by simp
  have hfin (d : ℕ) : Module.length A (Fin d → N) ≠ ⊤ := by
    rw [hfree]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top d) hN
  have hker : ∀ x : u.ker, g • x = 0 := by
    intro x
    apply Subtype.ext
    have hh := LinearMap.congr_fun hvu x
    simpa using hh.symm
  have hcoker : ∀ x : P ⧸ u.range, g • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change u.range.mkQ (g • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨v x,LinearMap.congr_fun huv x⟩
  have hk := length_torsion_subquotient_le u.ker.subtype LinearMap.id
    (Submodule.subtype_injective _) Function.surjective_id g hker (hfin n)
  rw [length_scalar_cokernel_pi_module] at hk
  let wc := u.range.mkQ.comp w
  have hwc : Function.Surjective wc := u.range.mkQ_surjective.comp hw
  have hc := length_torsion_subquotient_le LinearMap.id wc
    Function.injective_id hwc g hcoker (hfin c)
  rw [length_scalar_cokernel_pi_module] at hc
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

lemma length_le_quotient_generators {N : Type*} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N)
    {b : ℕ} (f : (Fin b → A) →ₗ[A] N) (hf : Function.Surjective f) :
    Module.length A N ≤ b * Module.length A (A ⧸ I) := by
  classical
  let P := Submodule.pi Set.univ (fun _ : Fin b => I)
  have hP : P ≤ f.ker := by
    intro x hx
    change f x = 0
    rw [pi_eq_sum_univ x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    exact Module.mem_annihilator.mp (hI (hx i (Set.mem_univ i))) _
  let q := P.liftQ f hP
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨P.mkQ y,rfl⟩
  calc
    Module.length A N ≤ Module.length A ((Fin b → A) ⧸ P) :=
      Module.length_le_of_surjective q hq
    _ = Module.length A (Fin b → A ⧸ I) :=
      (Submodule.quotientPi (fun _ : Fin b => I)).length_eq
    _ = _ := by simp

lemma length_scalar_cokernel_le_generators {N : Type*} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N)
    {b : ℕ} (f : (Fin b → A) →ₗ[A] N) (hf : Function.Surjective f) (g : A) :
    Module.length A (N ⧸ (LinearMap.lsmul A N g).range) ≤
      b * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  let P := (LinearMap.lsmul A N g).range
  let q := P.mkQ.comp f
  have hq : Function.Surjective q := P.mkQ_surjective.comp hf
  apply length_le_quotient_generators (I ⊔ Ideal.span {g}) _ q hq
  apply sup_le
  · intro a ha
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y,rfl⟩ := P.mkQ_surjective x
    rw [← map_smul, Module.mem_annihilator.mp (hI ha) y, map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y,rfl⟩ := P.mkQ_surjective x
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    exact ⟨y,rfl⟩

section Tensor
variable {E : Type*} [AddCommGroup E] [Module A E]
variable (N : Type*) [AddCommGroup N] [Module A N]

lemma tensor_length_isogeny (n c : ℕ) (g : A)
    (u : (Fin n → A) →ₗ[A] E) (v : E →ₗ[A] (Fin n → A))
    (huv : u.comp v = g • LinearMap.id) (hvu : v.comp u = g • LinearMap.id)
    (w : (Fin c → A) →ₗ[A] E) (hw : Function.Surjective w)
    (hN : Module.length A N ≠ ⊤) :
    Module.length A (N ⊗[A] E) ≤ n * Module.length A N +
        c * Module.length A (N ⧸ (LinearMap.lsmul A N g).range) ∧
    n * Module.length A N ≤ Module.length A (N ⊗[A] E) +
        n * Module.length A (N ⧸ (LinearMap.lsmul A N g).range) := by
  let e := TensorProduct.piScalarRight A A N (Fin n)
  let U := (TensorProduct.map (LinearMap.id : N →ₗ[A] N) u).comp e.symm.toLinearMap
  let V := e.toLinearMap.comp (TensorProduct.map (LinearMap.id : N →ₗ[A] N) v)
  let f := TensorProduct.piScalarRight A A N (Fin c)
  let W := (TensorProduct.map (LinearMap.id : N →ₗ[A] N) w).comp f.symm.toLinearMap
  have hUV : U.comp V = g • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change TensorProduct.map LinearMap.id u (e.symm (e (TensorProduct.map LinearMap.id v x))) = _
    rw [e.symm_apply_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, huv, TensorProduct.map_smul_right, TensorProduct.map_id]
  have hVU : V.comp U = g • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e (TensorProduct.map LinearMap.id v (TensorProduct.map LinearMap.id u (e.symm x))) = _
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, hvu, TensorProduct.map_smul_right, TensorProduct.map_id]
    change e (g • e.symm x) = g • x
    rw [map_smul,e.apply_symm_apply]
  have hW : Function.Surjective W :=
    (TensorProduct.map_surjective Function.surjective_id hw).comp f.symm.surjective
  exact length_module_isogeny n c g U V hUV hVU W hW hN
end Tensor

 

theorem finite_module_tensor_compare (A E : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : E →ₗ[A] E) ≠ 0) :
    ∃ (r c : ℕ) (g : A), 0 < r ∧ g ≠ 0 ∧
      ∀ (N : Type*) [AddCommGroup N] [Module A N],
      Module.length A N ≠ ⊤ → ∀ (I : Ideal A), I ≤ Module.annihilator A N →
      ∀ (b : ℕ) (f : (Fin b → A) →ₗ[A] N), Function.Surjective f →
      Module.length A (N ⊗[A] E) ≤ r * Module.length A N +
        (c*b) * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) ∧
      r * Module.length A N ≤ Module.length A (N ⊗[A] E) +
        (r*b) * Module.length A (A ⧸ (I ⊔ Ideal.span {g})) := by
  obtain ⟨r,g,hg,u,v,huv,hvu⟩ := finite_free_factorization A E
  obtain ⟨c,w,hw⟩ := Module.Finite.exists_fin' A E
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    apply hfaithful g hg
    rw [← huv]
    ext x
    have hz : v x = 0 := Subsingleton.elim _ _
    change u (v x) = 0
    rw [hz,map_zero]
  refine ⟨r,c,g,hr,hg,?_⟩
  intro N _ _ hN I hI b f hf
  have h := tensor_length_isogeny N r c g u v huv hvu w hw hN
  have he := length_scalar_cokernel_le_generators I hI f hf g
  constructor
  · apply h.1.trans
    apply add_le_add le_rfl
    simpa only [Nat.cast_mul,mul_assoc] using mul_le_mul_right he (c : ℕ∞)
  · apply h.2.trans
    apply add_le_add le_rfl
    simpa only [Nat.cast_mul,mul_assoc] using mul_le_mul_right he (r : ℕ∞)

open Filter
open scoped Topology
 

theorem finite_module_tensor_asymptoticENN (A E : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : E →ₗ[A] E) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ (N : ℕ → Type*) [∀ q, AddCommGroup (N q)] [∀ q, Module A (N q)]
      (I : ℕ → Ideal A) (w : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (b : ℕ),
      (∀ q, Module.length A (N q) ≠ ⊤) →
      (∀ q, I q ≤ Module.annihilator A (N q)) →
      (∀ q, ∃ f : (Fin b → A) →ₗ[A] N q, Function.Surjective f) →
      Tendsto (fun q => w q * (Module.length A (N q)).toENNReal) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        w q * (Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toENNReal) atTop (𝓝 0)) →
      Tendsto (fun q => w q * (Module.length A ((N q) ⊗[A] E)).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * a)) := by
  obtain ⟨r,c,g,hr,hg,h⟩ := finite_module_tensor_compare A E hfaithful
  refine ⟨r,hr,?_⟩
  intro N _ _ I w a b hN hI hgen hA hG
  have hb := ENNReal.Tendsto.const_mul (a := (r : ℝ≥0∞)) hA (Or.inr (by simp))
  have hec := ENNReal.Tendsto.const_mul (a := ((c*b : ℕ) : ℝ≥0∞)) (hG g hg) (Or.inr (by
    simp only [Nat.cast_mul]
    exact ENNReal.mul_ne_top (by simp) (by simp)))
  have hen := ENNReal.Tendsto.const_mul (a := ((r*b : ℕ) : ℝ≥0∞)) (hG g hg) (Or.inr (by
    simp only [Nat.cast_mul]
    exact ENNReal.mul_ne_top (by simp) (by simp)))
  simp only [mul_zero] at hec hen
  have hu := hb.add hec
  have hl := (ENNReal.tendsto_sub (a := (r : ℝ≥0∞)*a) (b := 0) (Or.inr (by simp))).comp
    (hb.prodMk_nhds hen)
  simp only [add_zero,tsub_zero] at hu hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro q
    obtain ⟨f,hf⟩ := hgen q
    obtain ⟨_,h₂⟩ := h (N q) (hN q) (I q) (hI q) b f hf
    have hh := mul_le_mul_right (ENat.toENNReal_mono h₂) (w q)
    simp only [ENat.toENNReal_add,ENat.toENNReal_mul,ENat.toENNReal_coe,
      mul_add,← mul_assoc] at hh
    rw [mul_comm (w q) (r : ℝ≥0∞)] at hh
    apply tsub_le_iff_right.mpr
    simpa only [Function.comp_apply, mul_assoc, mul_left_comm, mul_comm, Nat.cast_mul] using hh
  · intro q
    obtain ⟨f,hf⟩ := hgen q
    obtain ⟨h₁,_⟩ := h (N q) (hN q) (I q) (hI q) b f hf
    have hh := mul_le_mul_right (ENat.toENNReal_mono h₁) (w q)
    simp only [ENat.toENNReal_add,ENat.toENNReal_mul,ENat.toENNReal_coe,
      mul_add,← mul_assoc] at hh
    rw [mul_comm (w q) (r : ℝ≥0∞)] at hh
    simpa only [Function.comp_apply, mul_assoc, mul_left_comm, mul_comm, Nat.cast_mul] using hh

end Lech

end

end OAI
