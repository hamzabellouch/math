import Mathlib
import OAI.RingTheory.Multiplicity.IdealGradedLengthPiece

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
namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology nonZeroDivisors
variable {k : Type*} [Field k]

lemma fin_dimension_nat (h : ℕ) : Lech.dimension (MvPowerSeries (Fin h) k) = h := by
  simp [Lech.dimension,fin_dimension]

 

theorem finite_module_two_limits (h : ℕ) (hh : 0 < h) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries (Fin h) k) M] [Module.Finite (MvPowerSeries (Fin h) k) M] :
    ∃ n : ℕ,
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
  obtain ⟨n,hn⟩ := Lech.finite_module_asymptotic A M
  refine ⟨n,?_,?_⟩
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


namespace Lech.LocalAlgebra
open IsLocalRing
variable (A D : Type*) [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma quotient_length_eq (I : Ideal A)
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField D))) :
    Module.length A (D ⧸ I • (⊤ : Submodule A D)) =
      Module.length D (D ⧸ I.map (algebraMap A D)) := by
  rw [Ideal.smul_top_eq_map]
  rw [(Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A D))).length_eq]
  rw [IsLocalRing.length_restrictScalars A D _,
    Module.length_eq_of_surjective (R := ResidueField D) hres]
  simp

end Lech.LocalAlgebra


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  (h : ℕ) [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]

 

theorem parameter_powers_limit (hh : 0 < h) (hdim : Lech.dimension D = h)
    (hres : Function.Surjective (algebraMap (ResidueField (MvPowerSeries (Fin h) k))
      (ResidueField D)))
    (hprim : ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((Module.length D (D ⧸
      (Ideal.span (Set.range fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)).map
        (algebraMap (MvPowerSeries (Fin h) k) D))).toNat : ℝ) / (q : ℝ)^h)
      atTop (𝓝 (Lech.Primary.multiplicity ((maximalIdeal (MvPowerSeries (Fin h) k)).map
        (algebraMap (MvPowerSeries (Fin h) k) D)))) := by
  obtain ⟨r,hrm,hrp⟩ := finite_module_two_limits (k := k) h hh D
  have hm : Tendsto (Lech.Primary.normalizedColength ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D))) atTop (𝓝 (r : ℝ)) := by
    apply hrm.congr
    intro q
    rw [Lech.LocalAlgebra.quotient_length_eq _ _ _ hres,Ideal.map_pow]
    simp only [Lech.Primary.normalizedColength,Lech.Primary.colength,hdim]
  have he : Lech.Primary.multiplicity ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)) = (r : ℝ) := tendsto_nhds_unique (Lech.Primary.multiplicity_is_limit _ hprim) hm
  rw [he]
  apply hrp.congr
  intro q
  rw [Lech.LocalAlgebra.quotient_length_eq _ _ _ hres]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped Topology
variable {σ k D : Type*} [Fintype σ] [CommRing k] [CommRing D]
  (φ : k →+* D) (I : Ideal D) [IsAdicComplete I D]
  (z : σ → D) (hz : ∀ i, z i ∈ I)

 
def eval : MvPowerSeries σ k →+* D := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  exact MvPowerSeries.eval₂Hom (φ := φ) (continuous_of_discreteTopology)
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

lemma eval_C (a : k) : eval φ I z hz (C a) = φ a := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  have heval : MvPowerSeries.HasEval z :=
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  change MvPowerSeries.eval₂Hom (φ := φ) continuous_of_discreteTopology heval (C a) = _
  rw [MvPowerSeries.coe_eval₂Hom,MvPowerSeries.eval₂_C]

lemma eval_X (i : σ) : eval φ I z hz (X i) = z i := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  have heval : MvPowerSeries.HasEval z :=
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  change MvPowerSeries.eval₂Hom (φ := φ) continuous_of_discreteTopology heval (X i) = _
  rw [MvPowerSeries.coe_eval₂Hom,MvPowerSeries.eval₂_X]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [CommRing k]

def variablesIdeal : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range (X : σ → MvPowerSeries σ k))

omit [Fintype σ] in
lemma polynomial_variables_map :
    (MvPolynomial.idealOfVars σ k).map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := k)) =
      variablesIdeal σ k := by
  rw [MvPolynomial.idealOfVars,Ideal.map_span,← Set.range_comp]
  simp only [Function.comp_def,MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X,variablesIdeal]

lemma completion_variables_map :
    (variablesIdeal σ k).map (MvPowerSeries.toAdicCompletionAlgEquiv σ k).toRingEquiv.toRingHom =
      (MvPolynomial.idealOfVars σ k).map
        (algebraMap (MvPolynomial σ k) (AdicCompletion (MvPolynomial.idealOfVars σ k) (MvPolynomial σ k))) := by
  rw [← polynomial_variables_map,Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact MvPowerSeries.toAdicCompletion_coe f

 
lemma complete_variables : IsAdicComplete (variablesIdeal σ k) (MvPowerSeries σ k) := by
  exact inferInstanceAs (IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X)) (MvPowerSeries σ k))

end Lech.PowerSeries


namespace Lech.AdicNakayama
variable {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup M] [Module R M] (I : Ideal R) (f : P →ₗ[R] M)

lemma lift_power (h : f.range ⊔ I • ⊤ = ⊤) (n : ℕ) (x : M)
    (hx : x ∈ I^n • (⊤ : Submodule R M)) :
    ∃ y ∈ I^n • (⊤ : Submodule R P), x - f y ∈ I^(n+1) • (⊤ : Submodule R M) := by
  have hp : I^n • (⊤ : Submodule R M) =
      (I^n • (⊤ : Submodule R P)).map f ⊔ I^(n+1) • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'',Submodule.map_top,pow_succ, Submodule.mul_smul,← Submodule.smul_sup,h]
  rw [hp,Submodule.mem_sup] at hx
  obtain ⟨u,⟨y,hy,rfl⟩,v,hv,he⟩ := hx
  refine ⟨y,hy,?_⟩
  rw [← he,add_sub_cancel_left]
  exact hv

 

theorem surjective [IsPrecomplete I P] [IsHausdorff I M]
    (h : f.range ⊔ I • ⊤ = ⊤) : Function.Surjective f := by
  apply surjective_of_mkQ_comp_surjective (I := I)
  intro y
  obtain ⟨m,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective y
  have hm : m ∈ f.range ⊔ I • (⊤ : Submodule R M) := by rw [h]; trivial
  obtain ⟨_,⟨v,rfl⟩,w,hw,he⟩ := Submodule.mem_sup.mp hm
  refine ⟨v,?_⟩
  change (I • (⊤ : Submodule R M)).mkQ (f v) = _
  have hw0 : (I • (⊤ : Submodule R M)).mkQ w = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hw
  rw [← he,map_add,hw0,add_zero]

end Lech.AdicNakayama


namespace Lech.AdicNakayama
variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι]

lemma mem_smul_top_pi (v : ι → R) :
    v ∈ I • (⊤ : Submodule R (ι → R)) ↔ ∀ i, v i ∈ I := by
  classical
  constructor
  · intro hv i
    have hh := Submodule.smul_top_le_comap_smul_top I (LinearMap.proj i) hv
    simpa only [Submodule.mem_comap,LinearMap.proj_apply,smul_eq_mul,Ideal.mul_top] using hh
  · intro hv
    have he : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Pi.single_apply]
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hv i) (Submodule.mem_top))

lemma precomplete_pi [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  constructor
  intro f hf
  have hc i : ∀ {m n : ℕ}, m ≤ n → f m i ≡ f n i [SMOD (I^m • (⊤ : Submodule R R))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    simpa only [Pi.sub_apply,smul_eq_mul,Ideal.mul_top] using
      (mem_smul_top_pi (I^m) ι _).mp (SModEq.sub_mem.mp (hf hmn)) i
  choose L hL using (fun i => IsPrecomplete.prec (I := I) (M := R) inferInstance (hc i))
  refine ⟨L,fun n => ?_⟩
  rw [SModEq.sub_mem,mem_smul_top_pi]
  intro i
  simpa only [Pi.sub_apply,smul_eq_mul,Ideal.mul_top] using SModEq.sub_mem.mp (hL i n)

variable {M : Type*} [AddCommGroup M] [Module R M]

 

theorem finite_of_quotient [IsPrecomplete I R] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] : Module.Finite R M := by
  obtain ⟨n,g,hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • (⊤ : Submodule R M)))
  let := precomplete_pi I (Fin n)
  obtain ⟨f,hf⟩ := Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ g
    (I • (⊤ : Submodule R M)).mkQ_surjective
  apply Module.Finite.of_surjective f
  apply surjective_of_mkQ_comp_surjective (I := I)
  rw [hf]
  exact hg

end Lech.AdicNakayama


namespace Lech.Normalization
open IsLocalRing
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra k D]

lemma finite_primary_quotient (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (hres : Function.Surjective (algebraMap k (ResidueField D))) : Module.Finite k (D ⧸ I) := by
  let : IsArtinianRing (D ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
    rw [← Ideal.radical_minimalPrimes,hI,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  let : IsArtinian D (D ⧸ I) := isArtinian_of_surjective_algebraMap (R := D ⧸ I) (M := D ⧸ I)
    (S := D) Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (algebraMap (ResidueField k) (ResidueField D)) := by
    intro y
    obtain ⟨x,hx⟩ := hres y
    exact ⟨residue k x,hx⟩
  have hl : Module.length k (D ⧸ I) = Module.length D (D ⧸ I) := by
    rw [IsLocalRing.length_restrictScalars k D (D ⧸ I),Module.length_eq_of_surjective hs]
    simp
  have hfin : IsFiniteLength k (D ⧸ I) := Module.length_ne_top_iff.mp (by
    rw [hl]; exact Module.length_ne_top)
  let : IsNoetherian k (D ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
 

theorem finite_parameter_algebra
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    let : Algebra (MvPowerSeries σ k) D :=
      (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).toAlgebra
    Module.Finite (MvPowerSeries σ k) D := by
  let A := MvPowerSeries σ k
  let I := Lech.PowerSeries.variablesIdeal σ k
  let J : Ideal D := Ideal.span (Set.range z)
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra k D := φ.toAlgebra
  let : Algebra A D := ψ.toAlgebra
  let : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal D) z hz a).symm)
  have hmap : I.map (algebraMap A D) = J := by
    change (Ideal.span (Set.range (X : σ → A))).map (algebraMap A D) = J
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    exact congrArg Set.range (funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i))
  have hJ : J ≤ maximalIdeal D := Ideal.span_le.mpr (Set.range_subset_iff.mpr hz)
  let : IsHausdorff I D := IsHausdorff.of_map (I := I) (J := maximalIdeal D) (by rw [hmap]; exact hJ)
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables σ k).toIsPrecomplete
  let : Module.Finite k (D ⧸ J) := finite_primary_quotient J hprim hφ
  let : Module.Finite A (D ⧸ J) := Module.Finite.of_restrictScalars_finite k A (D ⧸ J)
  have hsub : I • (⊤ : Submodule A D) = J.restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule D D)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans (Submodule.Quotient.restrictScalarsEquiv A J)
  let : Module.Finite A (D ⧸ (I • (⊤ : Submodule A D))) := Module.Finite.equiv e.symm
  exact Lech.AdicNakayama.finite_of_quotient I

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

 
lemma exists_parameters : ∃ (n : ℕ) (z : Fin n → R),
    (∀ i, z i ∈ maximalIdeal R) ∧
    (Ideal.span (Set.range z)).radical = maximalIdeal R ∧
    ringKrullDim R = n := by
  classical
  obtain ⟨s,hs,hcard⟩ := (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
  let e := s.equivFin
  let z : Fin s.card → R := fun i => (e.symm i : R)
  have hrange : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).2
    · intro hr
      exact ⟨e ⟨r,hr⟩,by simp [z]⟩
  refine ⟨s.card,z,?_,?_,?_⟩
  · intro i
    exact hs.le (Ideal.subset_span (by rw [← hrange]; exact Set.mem_range_self i))
  · rw [hrange,← Ideal.sInf_minimalPrimes]
    apply le_antisymm (sInf_le hs)
    apply le_sInf
    intro Q hQ
    let : Q.IsPrime := hQ.isPrime
    exact hs.2 hQ.1 (le_maximalIdeal_of_isPrime Q)
  · rw [← maximalIdeal_height_eq_ringKrullDim,← hcard]
    rfl
end Lech.Normalization


namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p]

 
def frobeniusFactor (n : ℕ) : R ⧸ I →+* R ⧸ I^(p^n) :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk (I^(p^n))).comp (iterateFrobenius R p n)) (by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change x^(p^n) ∈ I^(p^n)
    exact Ideal.pow_mem_pow hx (p^n))

omit [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p] in
lemma frobeniusFactor_mk (n : ℕ) (x : R) :
    frobeniusFactor R I p n (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I^(p^n)) (x^(p^n)) := rfl

 
def stage (n : ℕ) : R ⧸ I →+* R ⧸ I^(p^n) :=
  (frobeniusFactor R I p n).comp (iterateFrobeniusEquiv (R ⧸ I) p n).symm.toRingHom

lemma stage_pow_mk (n : ℕ) (x : R) :
    stage R I p n ((Ideal.Quotient.mk I x)^(p^n)) =
      Ideal.Quotient.mk (I^(p^n)) (x^(p^n)) := by
  change frobeniusFactor R I p n
    ((iterateFrobeniusEquiv (R ⧸ I) p n).symm
      ((iterateFrobeniusEquiv (R ⧸ I) p n) (Ideal.Quotient.mk I x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

lemma power_strictMono : StrictMono (fun n : ℕ => p^n) :=
  pow_right_strictMono₀ (Nat.Prime.one_lt (Fact.out : p.Prime))

lemma stage_compatible (n : ℕ) :
    (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp
      (stage R I p (n+1)) = stage R I p n := by
  apply RingHom.ext
  intro x
  obtain ⟨y,hy⟩ := (iterateFrobeniusEquiv (R ⧸ I) p (n+1)).surjective x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← hy]
  change Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))
    (stage R I p (n+1) ((Ideal.Quotient.mk I a)^(p^(n+1)))) =
      stage R I p n ((Ideal.Quotient.mk I a)^(p^(n+1)))
  rw [stage_pow_mk]
  have he : (Ideal.Quotient.mk I a)^(p^(n+1)) =
      (Ideal.Quotient.mk I (a^p))^(p^n) := by
    rw [map_pow,← pow_mul,pow_succ']
  rw [he,stage_pow_mk]
  simp only [← pow_mul,pow_succ']
  rfl

variable [IsAdicComplete I R]

 

def sectionMap : R ⧸ I →+* R :=
  IsAdicComplete.StrictMono.liftRingHom I (power_strictMono p) (stage R I p)
    (fun {n} => stage_compatible R I p n)

lemma sectionMap_mod (n : ℕ) (x : R ⧸ I) :
    Ideal.Quotient.mk (I^(p^n)) (sectionMap R I p x) = stage R I p n x :=
  IsAdicComplete.StrictMono.mk_liftRingHom _ _ _ _ x

 
theorem sectionMap_rightInverse : Function.RightInverse (sectionMap R I p) (Ideal.Quotient.mk I) := by
  intro x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := sectionMap_mod R I p 0 (Ideal.Quotient.mk I a)
  have h0 := stage_pow_mk R I p 0 a
  apply Ideal.Quotient.eq.mpr
  have hh := Ideal.Quotient.eq.mp (h.trans (by simpa only [pow_zero,pow_one] using h0))
  simpa only [pow_zero,pow_one] using hh

lemma sectionMap_injective : Function.Injective (sectionMap R I p) :=
  (sectionMap_rightInverse R I p).injective

end Lech.CoefficientField
end

end OAI
