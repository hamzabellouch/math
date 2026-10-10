import Mathlib
import OAI.RingTheory.Multiplicity.PowerSeriesFinDimension

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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]
  [PerfectRing (IsLocalRing.ResidueField R) p]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

 

def localSection : IsLocalRing.ResidueField R →+* R := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk _) p (Nat.Prime.ne_zero Fact.out)
  let : PerfectRing (R ⧸ IsLocalRing.maximalIdeal R) p :=
    inferInstanceAs (PerfectRing (IsLocalRing.ResidueField R) p)
  exact sectionMap R (IsLocalRing.maximalIdeal R) p

lemma localSection_rightInverse :
    Function.RightInverse (localSection R p) (IsLocalRing.residue R) := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk _) p (Nat.Prime.ne_zero Fact.out)
  let : PerfectRing (R ⧸ IsLocalRing.maximalIdeal R) p :=
    inferInstanceAs (PerfectRing (IsLocalRing.ResidueField R) p)
  exact sectionMap_rightInverse R (IsLocalRing.maximalIdeal R) p

lemma localSection_injective : Function.Injective (localSection R p) :=
  (localSection_rightInverse R p).injective

end Lech.CoefficientField


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
lemma parameter_eval_finite (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).Finite :=
  finite_parameter_algebra φ hφ z hz hprim

include hφ in
lemma parameter_eval_injective (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (hdim : (Fintype.card σ : WithBot ℕ∞) ≤ ringKrullDim D) :
    Function.Injective (Lech.PowerSeries.eval φ (maximalIdeal D) z hz) := by
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra (MvPowerSeries σ k) D := ψ.toAlgebra
  let : Module.Finite (MvPowerSeries σ k) D := finite_parameter_algebra φ hφ z hz hprim
  exact injective_of_integral_dimension ψ (Algebra.IsIntegral.isIntegral)
    hdim (Lech.PowerSeries.dimension_le_variables σ k)

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable (D : Type*) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

include p in
 

theorem exists_finite_powerSeries_normalization :
    ∃ (n : ℕ) (ψ : MvPowerSeries (Fin n) (ResidueField D) →+* D),
      Function.Injective ψ ∧ ψ.Finite ∧ IsLocalHom ψ ∧
      Function.Surjective ((residue D).comp ψ) ∧ ringKrullDim D = n := by
  obtain ⟨n,z,hz,hprim,hdim⟩ := exists_parameters D
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  have hfin : ψ.Finite := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    simpa only [Fintype.card_fin,hdim] using (le_refl (n : WithBot ℕ∞)))
  have hint : ψ.IsIntegral := by
    let : Algebra (MvPowerSeries (Fin n) (ResidueField D)) D := ψ.toAlgebra
    let : Module.Finite (MvPowerSeries (Fin n) (ResidueField D)) D := hfin
    exact Algebra.IsIntegral.isIntegral
  refine ⟨n,ψ,hinj,hfin,hint.isLocalHom hinj,?_,hdim⟩
  intro a
  refine ⟨C a,?_⟩
  change residue D (Lech.PowerSeries.eval φ (maximalIdeal D) z hz (C a)) = a
  rw [Lech.PowerSeries.eval_C]
  exact Lech.CoefficientField.localSection_rightInverse D p a

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries Filter
open scoped Topology
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

 

theorem parameter_powers_multiplicity (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((Module.length D
      (D ⧸ Ideal.span (Set.range fun i : Fin h => z i^q))).toNat : ℝ) / (q : ℝ)^h)
      atTop (𝓝 (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) := by
  have hz : ∀ i, z i ∈ maximalIdeal D := fun i => by
    rw [← hprim]
    exact Ideal.le_radical (Ideal.subset_span ⟨i,rfl⟩)
  let A := MvPowerSeries (Fin h) k
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    rw [Fintype.card_fin,← hdim,Lech.dimension_cast])
  let : IsLocalHom (algebraMap A D) :=
    RingHom.IsIntegral.isLocalHom (f := ψ) Algebra.IsIntegral.isIntegral hinj
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hφ b
    refine ⟨residue A (C a),?_⟩
    rw [ResidueField.algebraMap_residue]
    change residue D (ψ (C a)) = b
    rw [Lech.PowerSeries.eval_C]
    exact ha
  have hm : (maximalIdeal A).map (algebraMap A D) = Ideal.span (Set.range z) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables,Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i
  have hp (q : ℕ) : (Ideal.span (Set.range fun i : Fin h => (X i : A)^q)).map
      (algebraMap A D) = Ideal.span (Set.range fun i => z i^q) := by
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    change ψ ((MvPowerSeries.X i)^q) = z i^q
    rw [map_pow,Lech.PowerSeries.eval_X]
  have ht := Lech.PowerSeries.parameter_powers_limit (k := k) (D := D) h hh hdim hres
    (by rwa [hm])
  change Tendsto (fun q : ℕ => ((Module.length D
    (D ⧸ (Ideal.span (Set.range fun i : Fin h => (X i : A)^q)).map
      (algebraMap A D))).toNat : ℝ) / (q : ℝ)^h) atTop
    (𝓝 (Lech.Primary.multiplicity ((maximalIdeal A).map (algebraMap A D)))) at ht
  rw [hm] at ht
  apply ht.congr
  intro q
  rw [hp q]

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing Filter
open scoped Topology ENNReal
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

omit [Field k] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma radical_span_powers {ι : Type*} (z : ι → D) (q : ℕ) (hq : q ≠ 0) :
    (Ideal.span (Set.range fun i => z i^q)).radical =
      (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) q (Nat.pos_of_ne_zero hq)
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨q,Ideal.subset_span ⟨i,rfl⟩⟩

theorem parameter_powers_multiplicity_enn (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((q : ℝ≥0∞)^h)⁻¹ * (Module.length D
      (D ⧸ Ideal.span (Set.range fun i : Fin h => z i^q))).toENNReal)
      atTop (𝓝 (ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (parameter_powers_multiplicity h hh hdim φ hφ z hprim)
  simp only [Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hf : Module.length D (D ⧸ Ideal.span (Set.range fun i => z i^q)) ≠ ⊤ := by
    have hf := Lech.Primary.length_ne_top
      (Ideal.span (Set.range fun i => z i^q))
      ((radical_span_powers z q (by omega)).trans hprim) 1
    rw [pow_one] at hf
    exact hf
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]
  congr 1
  exact congrArg ENat.toENNReal (ENat.natCast_toNat hf)

 

theorem parameter_frobenius_multiplicity_enn (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (a : ℕ) (ha : 0 < a) (p : ℕ) [Fact p.Prime] [CharP D p] :
    Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ * (Module.length D
      (D ⧸ (Ideal.span (Set.range fun i : Fin h => z i^a)).map
        (iterateFrobenius D p n))).toENNReal) atTop
      (𝓝 ((a : ℝ≥0∞)^h * ENNReal.ofReal
        (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
  have hp : Tendsto (fun n : ℕ => a*p^n) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop' ha
    exact tendsto_pow_atTop_atTop_of_one_lt (Fact.out : p.Prime).one_lt
  have ht := ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)^h)
    ((parameter_powers_multiplicity_enn h hh hdim φ hφ z hprim).comp hp)
    (Or.inr (by finiteness))
  apply ht.congr
  intro n
  dsimp only [Function.comp_def]
  have he : (Ideal.span (Set.range fun i : Fin h => z i^a)).map
      (iterateFrobenius D p n) = Ideal.span (Set.range fun i : Fin h => z i^(a*p^n)) := by
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact (pow_mul (z i) a (p^n)).symm
  rw [he,Nat.cast_mul,Nat.cast_pow,mul_pow,ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),← pow_mul]
  rw [← mul_assoc,← mul_assoc,ENNReal.mul_inv_cancel (by positivity) (by finiteness),one_mul]

end Lech.Normalization


namespace Lech
 

theorem finite_module_colength_error_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ (n c : ℕ) (g : A), 0 < n ∧ g ≠ 0 ∧ ∀ I : Ideal A,
      Module.length A (A ⧸ I) ≠ ⊤ →
      |((Module.length A (M ⧸ I • (⊤ : Submodule A M))).toNat : ℝ) -
        (n : ℝ) * ((Module.length A (A ⧸ I)).toNat : ℝ)| ≤
        (c : ℝ) * ((Module.length A (A ⧸ (I ⊔ Ideal.span {g}))).toNat : ℝ) := by
  obtain ⟨n,c,g,hn,hg,h⟩ := finite_module_colength_compare_pos A M hfaithful
  refine ⟨n,c+n,g,hn,hg,fun I hI => ?_⟩
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

open Filter
open scoped Topology
theorem finite_module_asymptotic_pos (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hfaithful : ∀ g : A, g ≠ 0 → g • (LinearMap.id : M →ₗ[A] M) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ (I : ℕ → Ideal A) (u : ℕ → ℝ) (a : ℝ),
      (∀ᶠ q in atTop, Module.length A (A ⧸ I q) ≠ ⊤) →
      (∀ᶠ q in atTop, 0 < u q) →
      Tendsto (fun q => ((Module.length A (A ⧸ I q)).toNat : ℝ) / u q) atTop (𝓝 a) →
      (∀ g : A, g ≠ 0 → Tendsto (fun q =>
        ((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q) atTop (𝓝 0)) →
      Tendsto (fun q => ((Module.length A (M ⧸ I q • (⊤ : Submodule A M))).toNat : ℝ) / u q)
        atTop (𝓝 ((n : ℝ) * a)) := by
  obtain ⟨n,c,g,hn,hg,h⟩ := finite_module_colength_error_pos A M hfaithful
  refine ⟨n,hn,fun I u a hI hu hA hG => ?_⟩
  apply tendsto_of_abs_sub_le (hA.const_mul (n : ℝ))
    (show Tendsto (fun q => (c : ℝ) *
      (((Module.length A (A ⧸ (I q ⊔ Ideal.span {g}))).toNat : ℝ) / u q)) atTop (𝓝 0) from by
        simpa using (hG g hg).const_mul (c : ℝ))
  filter_upwards [hI,hu] with q hI hu
  have hh := div_le_div_of_nonneg_right (h (I q) hI) hu.le
  simpa only [← mul_div_assoc,← sub_div,abs_div,abs_of_pos hu] using hh

end Lech


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology nonZeroDivisors
variable {k : Type*} [Field k]
 

theorem finite_module_two_limits_pos (h : ℕ) (hh : 0 < h) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries (Fin h) k) M] [Module.Finite (MvPowerSeries (Fin h) k) M]
    (hfaithful : ∀ g : MvPowerSeries (Fin h) k, g ≠ 0 → g • (LinearMap.id : M →ₗ[MvPowerSeries (Fin h) k] M) ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      Tendsto (fun q : ℕ => (h.factorial : ℝ) *
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ (maximalIdeal (MvPowerSeries (Fin h) k))^q • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) / (q : ℝ)^h)
        atTop (𝓝 (n : ℝ)) ∧
      Tendsto (fun q : ℕ =>
        ((Module.length (MvPowerSeries (Fin h) k)
          (M ⧸ Ideal.span (Set.range (fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)) • (⊤ : Submodule (MvPowerSeries (Fin h) k) M))).toNat : ℝ) /
          (q : ℝ)^h) atTop (𝓝 (n : ℝ)) := by
  let A := MvPowerSeries (Fin h) k
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let m := maximalIdeal A
  let J (q : ℕ) : Ideal A := Ideal.span (Set.range fun i : Fin h => (X i : A)^q)
  obtain ⟨n,hpos,hn⟩ := Lech.finite_module_asymptotic_pos A M hfaithful
  refine ⟨n,hpos,?_,?_⟩
  · have hbase : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ m^q)).toNat : ℝ) / ((q : ℝ)^h / h.factorial)) atTop (𝓝 1) := by
      apply (Lech.binomial_normalized_tendsto h).congr'
      filter_upwards [eventually_gt_atTop 0] with q hq
      rw [maximal_power_colength h hh q hq]
      simp only [ENat.toNat_natCast,div_div_eq_mul_div]
      ring
    have herr (g : A) (hg : g ≠ 0) : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ (m^q ⊔ Ideal.span {g}))).toNat : ℝ) /
          ((q : ℝ)^h / h.factorial)) atTop (𝓝 0) := by
      have ht := FrobeniusGrowth.ordinary_error_tendsto m
        (Ideal.IsPrime.radical inferInstance) (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
      rw [fin_dimension_nat] at ht
      convert ht.const_mul (h.factorial : ℝ) using 1
      · ext q
        simp only [div_div_eq_mul_div]
        ring
      · simp
    have ht := hn (fun q => m^q) (fun q => (q : ℝ)^h / h.factorial) 1
      (Eventually.of_forall (fun q => Lech.quotient_length_ne_top A q))
      ((eventually_gt_atTop 0).mono (fun q hq => by positivity)) hbase herr
    simp only [mul_one] at ht
    convert ht using 1
    ext q
    simp only [div_div_eq_mul_div]
    ring
  · have hbase : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ J q)).toNat : ℝ) / (q : ℝ)^h) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with q hq
      let : NeZero q := ⟨hq.ne'⟩
      have he := RootTower.variable_powers_colength (σ := Fin h) (k := k) q
      change Module.length A (A ⧸ J q) = _ at he
      rw [he]
      simp only [Fintype.card_fin]
      rw [← Nat.cast_pow, ENat.toNat_natCast, Nat.cast_pow]
      simp [hq.ne']
    have hfinite : ∀ᶠ q in atTop, Module.length A (A ⧸ J q) ≠ ⊤ := by
      filter_upwards [eventually_gt_atTop 0] with q hq
      let : NeZero q := ⟨hq.ne'⟩
      have he := RootTower.variable_powers_colength (σ := Fin h) (k := k) q
      change Module.length A (A ⧸ J q) = _ at he
      rw [he]
      exact ENat.natCast_ne_top _
    have herr (g : A) (hg : g ≠ 0) : Tendsto (fun q : ℕ =>
        ((Module.length A (A ⧸ (J q ⊔ Ideal.span {g}))).toNat : ℝ) / (q : ℝ)^h)
        atTop (𝓝 0) := by
      have ht := FrobeniusGrowth.parameter_error_tendsto h hh (X : Fin h → A)
        maximalIdeal_eq_variables.symm (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
      rwa [fin_dimension_nat] at ht
    have ht := hn J (fun q => (q : ℝ)^h) 1 hfinite
      ((eventually_gt_atTop 0).mono (fun q hq => by positivity)) hbase herr
    simpa only [mul_one] using ht

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  (h : ℕ) [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]

 
theorem exists_parameter_multiplicity_pos (hh : 0 < h) (hdim : Lech.dimension D = h)
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (ResidueField (MvPowerSeries (Fin h) k))
      (ResidueField D)))
    (hprim : ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)).radical = maximalIdeal D) :
    ∃ n : ℕ, 0 < n ∧ Lech.Primary.multiplicity ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)) = n := by
  obtain ⟨n,hn,ht,_⟩ := finite_module_two_limits_pos (k := k) h hh D (by
    intro g hg he
    apply hg
    apply hinj
    have he' := LinearMap.congr_fun he (1 : D)
    change g • (1 : D) = 0 at he'
    simpa only [Algebra.smul_def,mul_one,map_zero] using he')
  refine ⟨n,hn,?_⟩
  apply tendsto_nhds_unique (Lech.Primary.multiplicity_is_limit _ hprim)
  apply ht.congr
  intro q
  rw [Lech.LocalAlgebra.quotient_length_eq _ _ _ hres,Ideal.map_pow]
  simp only [Lech.Primary.normalizedColength,Lech.Primary.colength,hdim]

end Lech.PowerSeries


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]
 

theorem parameter_multiplicity_pos (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    0 < Lech.Primary.multiplicity (Ideal.span (Set.range z)) := by
  have hz : ∀ i, z i ∈ maximalIdeal D := fun i => by
    rw [← hprim]
    exact Ideal.le_radical (Ideal.subset_span ⟨i,rfl⟩)
  let A := MvPowerSeries (Fin h) k
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    rw [Fintype.card_fin,← hdim,Lech.dimension_cast])
  let : IsLocalHom (algebraMap A D) :=
    RingHom.IsIntegral.isLocalHom (f := ψ) Algebra.IsIntegral.isIntegral hinj
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hφ b
    refine ⟨residue A (C a),?_⟩
    rw [ResidueField.algebraMap_residue]
    change residue D (ψ (C a)) = b
    rw [Lech.PowerSeries.eval_C]
    exact ha
  have hm : (maximalIdeal A).map (algebraMap A D) = Ideal.span (Set.range z) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables,Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i
  obtain ⟨n,hn,hnum⟩ := Lech.PowerSeries.exists_parameter_multiplicity_pos
    (k := k) (D := D) h hh hdim hinj hres (by rwa [hm])
  rw [hm] at hnum
  rw [hnum]
  exact_mod_cast hn
end Lech.Normalization
end
end

end OAI
