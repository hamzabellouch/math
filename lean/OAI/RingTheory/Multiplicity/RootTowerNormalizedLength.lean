import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusIntermediatePowerMap

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
namespace Lech.RootTower
open scoped ENNReal
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]
  (C : Type*) [CommRing C] [CharP C p] [PerfectRing C p]
  [Algebra (PerfectClosure (MvPowerSeries σ k) p) C]

theorem normalizedLength_root_quotient (d : ℕ) (I : Ideal C) :
    normalizedLength σ k p (C ⧸ I.map (iterateFrobeniusEquiv C p d).symm) =
      ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * normalizedLength σ k p (C ⧸ I) :=
  normalizedLength_root_equiv σ k p d (quotientRootEquiv p d I)
end Lech.RootTower


namespace Lech.RootTower
variable {A B : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

 
lemma perfectMap_surjective (f : A →+* B)
    (h : ∃ n : ℕ, ∀ b : B, ∃ a : A, f a = b^(p^n)) :
    Function.Surjective (perfectMap p f) := by
  obtain ⟨n,hn⟩ := h
  intro z
  obtain ⟨⟨m,b⟩,rfl⟩ := PerfectClosure.mk_surjective B p z
  obtain ⟨a,ha⟩ := hn b
  refine ⟨rootMap A p (m+n) a,?_⟩
  rw [perfectMap_root,ha]
  change rootMap B p (m+n) (b^(p^n)) = rootMap B p m b
  simpa only [Nat.add_sub_cancel_left,iterateFrobenius_def] using
    rootMap_transition B p m (m+n) (Nat.le_add_right m n) b

end Lech.RootTower


namespace Lech.RootTower
open Lech.PerfectDomainStages
variable {A B D : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing D] [IsDomain D] [Algebra A B] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP D p]

def perfectAlgHom (f : B →ₐ[A] D) :
    PerfectClosure B p →ₐ[PerfectClosure A p] PerfectClosure D p where
  __ := perfectMap p f.toRingHom
  commutes' a := by
    change perfectMap p f.toRingHom (perfectMap p (algebraMap A B) a) =
      perfectMap p (algebraMap A D) a
    have hf : f.toRingHom.comp (algebraMap A B) = algebraMap A D := f.comp_algebraMap
    rw [← RingHom.comp_apply,perfectMap_comp,hf]

noncomputable def perfectAlgEquiv (f : B →ₐ[A] D) (hi : Function.Injective f)
    (he : ∃ e : ℕ, ∀ x : D, ∃ b : B, f b = x^(p^e)) :
    PerfectClosure B p ≃ₐ[PerfectClosure A p] PerfectClosure D p :=
  AlgEquiv.ofBijective (perfectAlgHom p f)
    ⟨perfectMap_injective p f.toRingHom hi, perfectMap_surjective p f.toRingHom he⟩

lemma perfectAlgEquiv_of (f : B →ₐ[A] D) (hi : Function.Injective f)
    (he : ∃ e : ℕ, ∀ x : D, ∃ b : B, f b = x^(p^e)) (b : B) :
    perfectAlgEquiv p f hi he (PerfectClosure.of B p b) = PerfectClosure.of D p (f b) :=
  perfectMap_of p f.toRingHom b
end Lech.RootTower


namespace Lech.FrobeniusIntermediate
open Lech.RootTower Lech.PerfectDomainStages
variable (σ k D : Type*) [Fintype σ] [Field k] [CommRing D] [IsDomain D]
    [Algebra (MvPowerSeries σ k) D]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
    (B : Subalgebra (MvPowerSeries σ k) D)
    (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
local instance : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
local instance : CharP B p := B.val.toRingHom.charP Subtype.val_injective p

 

theorem normalizedLength_intermediate_quotient (H : Ideal D) :
    normalizedLength σ k p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)) =
      ((p : ℝ≥0∞)^(e*Fintype.card σ))⁻¹ *
        normalizedLength σ k p ((PerfectClosure B p) ⧸
          (H.map (powerMap p B.toSubring e he)).map (PerfectClosure.of B p)) := by
  let C := PerfectClosure D p
  let E := perfectAlgEquiv p B.val Subtype.val_injective
    ⟨e,fun d => ⟨⟨d^(p^e),he d⟩,rfl⟩⟩
  let I := H.map (PerfectClosure.of D p)
  let J := (H.map (powerMap p B.toSubring e he)).map (PerfectClosure.of B p)
  have heq : J.map E.toRingEquiv.toRingHom = I.map (iterateFrobeniusEquiv C p e) := by
    dsimp only [J,I]
    change J.map E.toRingEquiv.toRingHom = I.map (iterateFrobeniusEquiv C p e : C →+* C)
    dsimp only [J,I]
    rw [Ideal.map_map,Ideal.map_map,Ideal.map_map]
    congr 1
    ext x
    change E (PerfectClosure.of B p (powerMap p B.toSubring e he x)) =
      iterateFrobeniusEquiv C p e (PerfectClosure.of D p x)
    refine (perfectAlgEquiv_of p B.val Subtype.val_injective
      ⟨e, fun d => ⟨⟨d^(p^e), he d⟩, rfl⟩⟩ (powerMap p B.toSubring e he x)).trans ?_
    rw [iterateFrobeniusEquiv_def,← map_pow]
    rfl
  have hl : normalizedLength σ k p ((PerfectClosure B p) ⧸ J) =
      normalizedLength σ k p (C ⧸ I.map (iterateFrobeniusEquiv C p e)) :=
    (regularTower σ k p).length_eq_of_equiv
      (Ideal.quotientEquivAlg J _ E heq.symm).toLinearEquiv
  rw [hl]
  have hroot := normalizedLength_root_quotient σ k p C e
    (I.map (iterateFrobeniusEquiv C p e))
  have heq' : (I.map (iterateFrobeniusEquiv C p e)).map (iterateFrobeniusEquiv C p e).symm = I := by
    exact Ideal.map_of_equiv (iterateFrobeniusEquiv C p e)
  rwa [heq'] at hroot
end Lech.FrobeniusIntermediate


namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Filter
open scoped ENNReal Topology
variable (h : ℕ) (k D : Type*) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type*) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

local instance : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
omit [IsNoetherianRing D] in
 

theorem exists_normalization_frobenius_limit
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) :
    ∃ r : ℕ, 0 < r ∧ ∀ (H : Ideal D),
      H.radical = IsLocalRing.maximalIdeal D →
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : IsNoetherianRing B.toSubring := inferInstanceAs (IsNoetherianRing B)
  let : IsLocalRing B.toSubring := inferInstanceAs (IsLocalRing B)
  let : IsLocalHom B.toSubring.subtype := inferInstanceAs (IsLocalHom (algebraMap B D))
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let : IsLocalHom (algebraMap A B) := ⟨fun x hx =>
    isUnit_of_map_unit (algebraMap A D) x (by
      simpa only [← IsScalarTower.algebraMap_apply A B D] using hx.map (algebraMap B D))⟩
  let : Module.Finite B D := Module.Finite.of_restrictScalars_finite A B D
  have hfb : Function.Injective (algebraMap A B) := by
    intro x y hxy
    exact hf (by simpa only [← IsScalarTower.algebraMap_apply A B D] using
      (congrArg (algebraMap B D) hxy))
  have hresBD : Function.Surjective (algebraMap (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField D)) := by
    intro x
    obtain ⟨a,ha⟩ := hres x
    exact ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a,
      (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha⟩
  have hresAB : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := by
    intro b
    obtain ⟨a,ha⟩ := hres (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D) b)
    refine ⟨a,(algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)).injective ?_⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha
  have hdim : Lech.dimension B = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A B)
      (Algebra.IsIntegral.isIntegral : (algebraMap A B).IsIntegral) hfb
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast B
    rw [hd] at hh
    exact_mod_cast hh
  have hdimSub : Lech.dimension B.toSubring = h := hdim
  obtain ⟨e,he⟩ := uniform_power A D K L p
  obtain ⟨r,hr,hlim⟩ := Lech.FrobeniusIntermediate.exists_positive_rank_transfer p B.toSubring
  refine ⟨r,hr,fun H hH => ?_⟩
  let G := H.map (Lech.FrobeniusIntermediate.powerMap p B.toSubring e he)
  have hG : G.radical = IsLocalRing.maximalIdeal B :=
    Lech.FrobeniusIntermediate.map_radical_primary p B.toSubring e he H hH
  have ht := frobenius_colength_tendsto h k B p K E hfb hresAB G hG
  have hout := hlim e he hresBD H hH
    (normalizedLength (Fin h) k p ((PerfectClosure B p) ⧸ G.map (PerfectClosure.of B p)))
    (by
      rw [hdimSub]
      apply ht.congr
      intro n
      rfl)
  have heq := Lech.FrobeniusIntermediate.normalizedLength_intermediate_quotient
    (Fin h) k D p B e he H
  simp only [Fintype.card_fin] at heq
  rw [heq]
  simpa only [hdim, hdimSub,mul_left_comm] using hout
end Lech.SeparableOrder


namespace Lech.NormalizedLength.Tower
open Filter
open scoped Topology
variable {L : Type*} [CommRing L] (T : Tower L)
  {M : Type*} [AddCommGroup M] [Module L M]

lemma length_fin (n : ℕ) : T.length (Fin n → M) = n * T.length M := by
  induction n with
  | zero => simp [T.length_zero]
  | succ n ih =>
    rw [T.length_eq_of_equiv (Fin.consLinearEquiv L (fun _ : Fin (n+1) => M)).symm,
      T.length_prod, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

 
lemma exists_length_le_mul_quotient [Module.Finite L M] :
    ∃ r : ℕ, ∀ I : Ideal L, (∀ a ∈ I, ∀ x : M, a • x = 0) →
      T.length M ≤ r * T.length (L ⧸ I) := by
  classical
  obtain ⟨r,s,hs⟩ := Module.Finite.exists_fin (R := L) (M := M)
  refine ⟨r,fun I hI => ?_⟩
  let fi (i : Fin r) : (L ⧸ I) →ₗ[L] M :=
    I.liftQ (LinearMap.toSpanSingleton L M (s i)) (by
      intro a ha
      exact hI a ha (s i))
  let f : (Fin r → L ⧸ I) →ₗ[L] M := LinearMap.lsum L (fun _ : Fin r => L ⧸ I) L fi
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    apply le_antisymm le_top
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨Pi.single i (Ideal.Quotient.mk I 1),?_⟩
    rw [LinearMap.lsum_piSingle]
    change (1 : L) • s i = s i
    exact one_smul _ _
  exact (T.length_le_of_surjective f hf).trans_eq (T.length_fin r)

 

theorem length_eq_zero_of_small_annihilators (I : ℕ → Ideal L)
    (hI : ∀ n a, a ∈ I n → ∀ x : M, a • x = 0)
    (hlim : Tendsto (fun n => T.length (L ⧸ I n)) atTop (𝓝 0)) :
    T.length M = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro s
  let U := Submodule.span L (s : Set M)
  have : Module.Finite L U := Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
  obtain ⟨r,hr⟩ := T.exists_length_le_mul_quotient (M := U)
  have hU : T.length U ≤ 0 := by
    have hlim' := ENNReal.Tendsto.const_mul (a := (r : ℝ≥0∞)) hlim (Or.inr (by simp))
    simp only [mul_zero] at hlim'
    apply ge_of_tendsto hlim'
    exact Filter.Eventually.of_forall fun n => hr (I n) (fun a ha x =>
      Subtype.ext (by exact hI n a ha x))
  exact (T.finiteLength_le_length_of_subset s U Submodule.subset_span).trans hU
end Lech.NormalizedLength.Tower


namespace Lech.RootTower
open Filter
open scoped ENNReal Topology TensorProduct nonZeroDivisors
variable (h : ℕ) (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma normalizedLength_base_root_quotient (n : ℕ) (J : Ideal (MvPowerSeries (Fin h) k)) :
    normalizedLength (Fin h) k p ((PerfectClosure (MvPowerSeries (Fin h) k) p) ⧸
      J.map (rootMap (MvPowerSeries (Fin h) k) p n)) =
    ((p : ℝ≥0∞) ^ (n*h))⁻¹ * (Module.length (MvPowerSeries (Fin h) k)
      ((MvPowerSeries (Fin h) k) ⧸ J)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot P J
  have he := (regularTower (Fin h) k p).length_eq_of_equiv e.toLinearEquiv
  change normalizedLength (Fin h) k p (P ⧸ J.map (rootMap A p n)) =
    normalizedLength (Fin h) k p (P ⊗[A] (A ⧸ J)) at he
  rw [he]
  simpa only [Fintype.card_fin] using normalizedLength_rootBaseChange (Fin h) k p n (A ⧸ J)

omit [PerfectRing k p] in
lemma frobenius_root_ideal (H : Ideal (MvPowerSeries (Fin h) k))
    (g : MvPowerSeries (Fin h) k) (n : ℕ) :
    (H.map (iterateFrobenius (MvPowerSeries (Fin h) k) p n) ⊔ Ideal.span {g}).map
      (rootMap (MvPowerSeries (Fin h) k) p n) =
    H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
      Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g} := by
  rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton,Ideal.map_map]
  congr 2
  apply DFunLike.ext
  intro a
  exact rootMap_transition (MvPowerSeries (Fin h) k) p 0 n (Nat.zero_le n) a

 

lemma root_scalar_quotient_tendsto (H : Ideal (MvPowerSeries (Fin h) k))
    (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0) :
    Tendsto (fun n : ℕ => normalizedLength (Fin h) k p
      ((PerfectClosure (MvPowerSeries (Fin h) k) p) ⧸
        (H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
          Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g}))) atTop (𝓝 0) := by
  let : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _
  have hdim : Lech.dimension (MvPowerSeries (Fin h) k) = h := by
    have hd := Lech.dimension_cast (MvPowerSeries (Fin h) k)
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    exact_mod_cast hd
  have ht := Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal H hH
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg) p
  rw [hdim] at ht
  apply ht.congr
  intro n
  symm
  rw [← frobenius_root_ideal]
  exact normalizedLength_base_root_quotient h k p n _

 
lemma normalizedLength_eq_zero_of_root_annihilated
    (M : Type*) [AddCommGroup M] [Module (PerfectClosure (MvPowerSeries (Fin h) k) p) M]
    (H : Ideal (MvPowerSeries (Fin h) k))
    (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0)
    (hHM : ∀ a ∈ H, ∀ x : M, PerfectClosure.of (MvPowerSeries (Fin h) k) p a • x = 0)
    (hgM : ∀ n x, rootMap (MvPowerSeries (Fin h) k) p n g • (x : M) = 0) :
    normalizedLength (Fin h) k p M = 0 := by
  apply (regularTower (Fin h) k p).length_eq_zero_of_small_annihilators
    (fun n => H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
      Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g})
  · intro n
    have hh : H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ≤ Module.annihilator _ M := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact Module.mem_annihilator.mpr (hHM a ha)
    have hg' : Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g} ≤ Module.annihilator _ M := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact Module.mem_annihilator.mpr (hgM n)
    intro a ha x
    exact Module.mem_annihilator.mp ((sup_le hh hg') ha) x
  · exact root_scalar_quotient_tendsto h k p H hH hg
end Lech.RootTower


namespace Lech
open scoped TensorProduct
variable {A P M N : Type*} [CommRing A] [CommRing P] [Algebra A P]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
lemma baseChange_scalar_factorization (u : M →ₗ[A] N) (v : N →ₗ[A] M)
    (b : A) (hb : u.comp v = b • LinearMap.id) :
    (u.baseChange P).comp (v.baseChange P) = (algebraMap A P b) • LinearMap.id := by
  rw [← LinearMap.baseChange_comp,hb,LinearMap.baseChange_smul,LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  change b • x = (algebraMap A P b) • x
  exact (algebraMap_smul P b x).symm
end Lech


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

 

theorem exists_root_finite_free_factorization
    (hi : ∀ n, Function.Injective (tensorMap A D p n))
    (hg : ∃ g : A, g ≠ 0 ∧ ∀ n c, rootMap A p n g • c ∈ stage A D p n) :
    ∃ (r : ℕ) (a : A), a ≠ 0 ∧ ∀ n : ℕ,
      ∃ (u : (Fin r → PerfectClosure A p) →ₗ[PerfectClosure A p] PerfectClosure D p)
        (v : PerfectClosure D p →ₗ[PerfectClosure A p] (Fin r → PerfectClosure A p)),
        u.comp v = rootMap A p n a • LinearMap.id := by
  classical
  obtain ⟨g,hgn,hgc⟩ := hg
  obtain ⟨r,b,hbn,u,v,huv,_⟩ := Lech.finite_free_factorization A D
  refine ⟨r,b*g,mul_ne_zero hbn hgn,fun n => ?_⟩
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let B := stage A D p n
  let e := (tensorEquiv A D p n (hi n)).toLinearEquiv
  let q := ((Pi.basisFun A (Fin r)).baseChange P).equivFun
  let c : C →ₗ[P] B := (Lech.Conductor.linearMap B (rootMap A p n g) (hgc n)).restrictScalars P
  let j : B →ₗ[P] C := B.val.toLinearMap
  let U := j.comp (e.toLinearMap.comp ((u.baseChange P).comp q.symm.toLinearMap))
  let V := q.toLinearMap.comp ((v.baseChange P).comp (e.symm.toLinearMap.comp c))
  refine ⟨U,V,?_⟩
  have hvu := Lech.baseChange_scalar_factorization (P := P) u v b huv
  apply LinearMap.ext
  intro x
  change j (e ((u.baseChange P) (q.symm (q ((v.baseChange P) (e.symm (c x))))))) =
    rootMap A p n (b*g) • x
  rw [q.symm_apply_apply]
  have hh := LinearMap.congr_fun hvu (e.symm (c x))
  change (u.baseChange P) ((v.baseChange P) (e.symm (c x))) =
    rootMap A p n b • e.symm (c x) at hh
  rw [hh,map_smul,e.apply_symm_apply,map_smul]
  change rootMap A p n b • (rootMap A p n g • x) = _
  rw [← mul_smul,← map_mul]
end Lech.PerfectDomainStages

open scoped Classical Pointwise
namespace Lech.PowerSeries
open MvPowerSeries RingTheory.Sequence
variable (k : Type*) [Field k]

lemma killSucc_surjective (h : ℕ) :
    Function.Surjective (killCompl (R := k) (Fin.succEmb h)) := by
  intro f
  exact ⟨rename (Fin.succEmb h) f,killCompl_rename_app _⟩

lemma killSucc_ker (h : ℕ) :
    RingHom.ker (killCompl (R := k) (Fin.succEmb h)).toRingHom =
      Ideal.span {(X (0 : Fin (h+1)) : MvPowerSeries (Fin (h+1)) k)} := by
  apply le_antisymm
  · intro f hf
    apply Ideal.mem_span_singleton.mpr
    apply X_dvd_iff.mpr
    intro d hd
    have he : d ∈ Set.range (Finsupp.embDomain (Fin.succEmb h)) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro i hi
      have hn : i ≠ 0 := by
        intro hz
        subst i
        exact (Finsupp.mem_support_iff.mp hi) hd
      exact ⟨i.pred hn,Fin.succ_pred i hn⟩
    obtain ⟨a,rfl⟩ := he
    have hx := congrArg (coeff a) hf
    exact hx
  · rw [Ideal.span_singleton_le_iff_mem]
    apply killCompl_X_eq_zero
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi

lemma variables_weaklyRegular (h : ℕ) :
    IsWeaklyRegular (MvPowerSeries (Fin h) k)
      (List.ofFn (X : Fin h → MvPowerSeries (Fin h) k)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [List.ofFn_succ,isWeaklyRegular_cons_iff]
    constructor
    · apply IsSMulRegular.of_ne_zero
      intro hz
      have hx := congrArg (coeff (Finsupp.single 0 1)) hz
      simp at hx
    · let A := MvPowerSeries (Fin (h+1)) k
      let B := MvPowerSeries (Fin h) k
      let f : A →+* B := (killCompl (R := k) (Fin.succEmb h)).toRingHom
      let : Algebra A B := f.toAlgebra
      let q : A →ₗ[A] B := Algebra.linearMap A B
      have hker : q.ker = (X (0 : Fin (h+1)) : A) • (⊤ : Submodule A A) := by
        change RingHom.ker f = _
        rw [killSucc_ker]
        rw [← Submodule.ideal_span_singleton_smul]
        exact (Ideal.mul_top _).symm
      let e : QuotSMulTop (X (0 : Fin (h+1)) : A) A ≃ₗ[A] B :=
        (Submodule.quotEquivOfEq _ _ hker.symm).trans
          (q.quotKerEquivOfSurjective (killSucc_surjective k h))
      apply (e.isWeaklyRegular_congr _).mpr
      apply (isWeaklyRegular_map_algebraMap_iff B B _).mp
      have hm : (List.ofFn (fun i : Fin h => (X i.succ : A))).map (algebraMap A B) =
          List.ofFn (X : Fin h → B) := by
        rw [List.map_ofFn]
        congr 1
        funext i
        exact killCompl_X (e := Fin.succEmb h) i
      rw [hm]
      exact ih
end Lech.PowerSeries
end
end

end OAI
