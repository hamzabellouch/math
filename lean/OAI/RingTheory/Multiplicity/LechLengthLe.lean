import Mathlib
import OAI.RingTheory.Multiplicity.SubalgebraStageFromBase

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
namespace Lech

lemma length_le_add_of_exact {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hg : Function.Surjective g)
    (he : Function.Exact f g) :
    Module.length R M ≤ Module.length R N + Module.length R P := by
  let f' : N →ₗ[R] g.ker := f.codRestrict g.ker (fun n => by
    rw [LinearMap.exact_iff.mp he]
    exact ⟨n, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨m, hm⟩
    rw [LinearMap.exact_iff.mp he] at hm
    obtain ⟨n, rfl⟩ := hm
    exact ⟨n, rfl⟩
  rw [Module.length_eq_add_of_exact g.ker.subtype g g.ker.subtype_injective hg
    (LinearMap.exact_subtype_ker_map g)]
  exact add_le_add (Module.length_le_of_surjective f' hf') le_rfl

namespace ParameterBound
variable {R : Type*} [CommRing R]

lemma length_mul_le (J : Ideal R) (x y : R) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x * y})) ≤
      Module.length R (R ⧸ (J ⊔ Ideal.span {x})) +
        Module.length R (R ⧸ (J ⊔ Ideal.span {y})) := by
  let A := J ⊔ Ideal.span {x}
  let B := J ⊔ Ideal.span {x * y}
  let C := J ⊔ Ideal.span {y}
  have hmul : ∀ z ∈ A, y * z ∈ B := by
    intro z hz
    obtain ⟨j, hj, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [mul_add]
    apply B.add_mem
    · exact Submodule.mem_sup_left (J.mul_mem_left y hj)
    · apply Submodule.mem_sup_right
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨a, by ring⟩
  let f : (R ⧸ A) →ₗ[R] R ⧸ B :=
    A.liftQ (B.mkQ.comp (LinearMap.lsmul R R y)) (by
      intro z hz
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hmul z hz))
  have hBC : B ≤ C := by
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩)
  let g : (R ⧸ B) →ₗ[R] R ⧸ C := B.mapQ C LinearMap.id hBC
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨r, rfl⟩ := C.mkQ_surjective q
    exact ⟨B.mkQ r, rfl⟩
  apply length_le_add_of_exact f g hg
  rw [LinearMap.exact_iff]
  ext q
  obtain ⟨r, rfl⟩ := B.mkQ_surjective q
  constructor
  · intro hr
    change C.mkQ r = 0 at hr
    have hrC := (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨j, hj, t, ht, he⟩ := Submodule.mem_sup.mp hrC
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    refine ⟨A.mkQ a, ?_⟩
    change B.mkQ (y * a) = B.mkQ r
    apply (Submodule.Quotient.eq _).mpr
    rw [← he]
    have he' : y * a - (j + a * y) = -j := by ring
    rw [he']
    exact B.neg_mem (Submodule.mem_sup_left hj)
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := A.mkQ_surjective a
    change B.mkQ (y * a) = B.mkQ r at ha
    change g (B.mkQ r) = 0
    rw [← ha]
    change C.mkQ (y * a) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩)

lemma length_pow_le (J : Ideal R) (x : R) (n : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x ^ n})) ≤
      n * Module.length R (R ⧸ (J ⊔ Ideal.span {x})) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (length_mul_le J (x ^ n) x).trans (add_le_add ih le_rfl)

lemma length_parameter_powers_le (n : ℕ) (x : Fin n → R) (J : Ideal R) (N : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range (fun i => x i ^ N)))) ≤
      (N : ℕ∞) ^ n * Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range x))) := by
  induction n generalizing J with
  | zero =>
      have he : (fun i : Fin 0 => x i ^ N) = x := funext (fun i => Fin.elim0 i)
      rw [he, pow_zero, one_mul]
  | succ n ih =>
      rw [Fin.range_fin_succ, Ideal.span_insert, Fin.range_fin_succ, Ideal.span_insert]
      have h1 := length_pow_le (J ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N)))
         (x 0) N
      have h2 := ih (fun i => x i.succ) (J ⊔ Ideal.span {x 0})
      have h2' := mul_le_mul_right h2 (N : ℕ∞)
      rw [sup_right_comm J] at h2'
      have h := h1.trans h2'
      change Module.length R (R ⧸ (J ⊔ (Ideal.span {x 0 ^ N} ⊔
        Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N))))) ≤
        (N : ℕ∞) ^ (n + 1) * Module.length R (R ⧸ (J ⊔
          (Ideal.span {x 0} ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ)))))
      rw [← sup_assoc, sup_right_comm J, ← sup_assoc, pow_succ', mul_assoc]
      exact h

end ParameterBound
end Lech


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

lemma colength_polynomial_bound :
    ∃ C : ℕ, ∀ N : ℕ, colength R N ≤ N ^ dimension R * C := by
  classical
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨s, hp, hc⟩ := m.exists_finset_card_eq_height_of_isNoetherianRing
  let I := Ideal.span (s : Set R)
  let x : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hx : Set.range x = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r, hr⟩, congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  have hxm (i : Fin s.card) : x i ∈ m :=
    hp.le (Ideal.subset_span (by rw [← hx]; exact Set.mem_range_self i))
  have hcard : s.card = dimension R := by
    have h := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hc
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← dimension_cast R] at h
    exact Nat.cast_injective (WithBot.coe_injective h)
  let : IsArtinianRing (R ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
  have hfinite : Module.length R (R ⧸ I) ≠ ⊤ := by
    rw [Module.length_eq_of_surjective (R := R ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top
  let C := (Module.length R (R ⧸ I)).toNat
  have hC : (C : ℕ∞) = Module.length R (R ⧸ I) := ENat.natCast_toNat hfinite
  refine ⟨C, fun N => ?_⟩
  have hpow : Ideal.span (Set.range (fun i => x i ^ N)) ≤ m ^ N := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_pow (hxm i) N
  have h1 := length_quotient_le R hpow
  have h2 := ParameterBound.length_parameter_powers_le s.card x (⊥ : Ideal R) N
  rw [bot_sup_eq, bot_sup_eq, hx] at h2
  have h := h1.trans h2
  rw [hcard, ← hC, ← Nat.cast_pow, ← Nat.cast_mul] at h
  rw [← colength_cast R] at h
  exact ENat.natCast_le_natCast.mp h
end Lech

open scoped BigOperators
namespace Lech

variable {R : Type*} [CommRing R]

 

end Lech


namespace Lech.FrobeniusGrowth
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]

 
def powerIdeal (H : Ideal R) (q : ℕ) : Ideal R :=
  Ideal.span ((fun x : R => x^q) '' (H : Set R))

lemma pow_mem_powerIdeal (H : Ideal R) (q : ℕ) {x : R} (hx : x ∈ H) :
    x^q ∈ powerIdeal H q := Ideal.subset_span ⟨x,hx,rfl⟩

lemma powerIdeal_eq_map (H : Ideal R) (p n : ℕ) [Fact p.Prime] [CharP R p] :
    powerIdeal H (p^n) = H.map (iterateFrobenius R p n) := by
  rw [← Ideal.span_eq H, Ideal.map_span, Ideal.span_eq]
  rfl

lemma pigeonhole (H : Ideal R) (hH : H.FG) :
    ∃ t : ℕ, ∀ q : ℕ, 1 ≤ q → H^(t*(q-1)+1) ≤ powerIdeal H q := by
  classical
  obtain ⟨s,hs⟩ := hH
  let z : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hz : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r,hr⟩,congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  refine ⟨s.card,fun q hq => ?_⟩
  have h := (Lech.parameter_power_cofinality s.card q hq z).1
  rw [hz,hs] at h
  refine h.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i,rfl⟩
  apply pow_mem_powerIdeal
  rw [← hs]
  exact Ideal.subset_span (by rw [← hz]; exact Set.mem_range_self i)

lemma linear_power_containment [IsNoetherianRing R] [IsLocalRing R]
    (H : Ideal R) (hH : H.radical = IsLocalRing.maximalIdeal R) :
    ∃ c : ℕ, ∀ q : ℕ, 1 ≤ q → (IsLocalRing.maximalIdeal R)^(c*q) ≤ powerIdeal H q := by
  obtain ⟨a,ha⟩ := H.exists_radical_pow_le_of_fg H.radical.fg_of_isNoetherianRing
  rw [hH] at ha
  obtain ⟨t,ht⟩ := pigeonhole H H.fg_of_isNoetherianRing
  refine ⟨a*(t+1),fun q hq => ?_⟩
  have he : t*(q-1)+1 ≤ (t+1)*q := by
    calc
      _ ≤ t*q+q := Nat.add_le_add (Nat.mul_le_mul_left t (Nat.sub_le q 1)) hq
      _ = _ := by ring
  calc
    _ = ((IsLocalRing.maximalIdeal R)^a)^((t+1)*q) := by rw [← pow_mul]; congr 1; ring
    _ ≤ H^((t+1)*q) := pow_le_pow_left' ha _
    _ ≤ H^(t*(q-1)+1) := Ideal.pow_le_pow_right he
    _ ≤ powerIdeal H q := ht q hq

lemma quotient_power_length (I J : Ideal R) (n : ℕ) :
    Module.length (R ⧸ J) ((R ⧸ J) ⧸ (I.map (Ideal.Quotient.mk J)) ^ n) =
      Module.length R (R ⧸ (I ^ n ⊔ J)) := by
  rw [← Ideal.map_pow]
  have he := (DoubleQuot.quotQuotEquivQuotSupₐ R J (I ^ n)).toLinearEquiv.length_eq
  rw [sup_comm] at he
  have hlen := Module.length_eq_of_surjective (S := R) (R := R ⧸ J)
    (M := (R ⧸ J) ⧸ (I ^ n).map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk_surjective (I := J))
  exact hlen.symm.trans he

variable [IsNoetherianRing R] [IsLocalRing R]

lemma quotient_dimension_lt {g : R} (hg : g ∈ R⁰) [IsLocalRing (R ⧸ Ideal.span {g})] :
    Lech.dimension (R ⧸ Ideal.span {g}) < Lech.dimension R := by
  have hh := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hg
  rw [← Lech.dimension_cast (R ⧸ Ideal.span {g}),← Lech.dimension_cast R] at hh
  have hh' : (Lech.dimension (R ⧸ Ideal.span {g}) : WithBot ℕ∞) +
      (1 : WithBot ℕ∞) ≤ (Lech.dimension R : WithBot ℕ∞) := hh
  exact_mod_cast hh'

lemma quotient_colength_bound (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q →
      Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≤
        (C : ℕ∞) * (q : ℕ∞)^(Lech.dimension R - 1) := by
  by_cases hu : IsUnit g
  · refine ⟨0,fun q hq => ?_⟩
    simp [Ideal.span_singleton_eq_top.mpr hu]
  have hJ : Ideal.span ({g} : Set R) ≠ ⊤ := fun hh => hu (Ideal.span_singleton_eq_top.mp hh)
  let B := R ⧸ Ideal.span {g}
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hm : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {g})) =
      IsLocalRing.maximalIdeal B := by
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact IsLocalRing.le_maximalIdeal hJ
  obtain ⟨c,hc⟩ := linear_power_containment H hH
  obtain ⟨C,hC⟩ := Lech.colength_polynomial_bound B
  refine ⟨c^(Lech.dimension B)*C,fun q hq => ?_⟩
  have hh := Lech.length_quotient_le R
    (sup_le_sup_right (hc q hq) (Ideal.span {g}))
  rw [← quotient_power_length,hm,← Lech.colength_cast B] at hh
  have hdim : Lech.dimension B ≤ Lech.dimension R - 1 := by
    have hh := quotient_dimension_lt hg
    change Lech.dimension B < Lech.dimension R at hh
    omega
  have hn := (hC (c*q)).trans (show (c*q)^Lech.dimension B*C ≤
      (c^Lech.dimension B*C)*q^(Lech.dimension R-1) from by
    rw [mul_pow,mul_right_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq hdim))
  exact hh.trans (by exact_mod_cast hn)

open Filter
open scoped Topology

 
theorem normalized_error_bound (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q →
      ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R ≤ (C : ℝ) / q := by
  obtain ⟨C,hC⟩ := quotient_colength_bound H hH hg
  by_cases hd : Lech.dimension R = 0
  · have hu : IsUnit g := by
      by_contra hu
      have hJ : Ideal.span ({g} : Set R) ≠ ⊤ := fun hh => hu (Ideal.span_singleton_eq_top.mp hh)
      have : Nontrivial (R ⧸ Ideal.span {g}) := Ideal.Quotient.nontrivial_iff.mpr hJ
      have : IsLocalRing (R ⧸ Ideal.span {g}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have := quotient_dimension_lt hg
      omega
    exact ⟨0,fun q hq => by simp [Ideal.span_singleton_eq_top.mpr hu]⟩
  refine ⟨C,fun q hq => ?_⟩
  have hb := hC q hq
  have hf : Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [← Nat.cast_pow,← Nat.cast_mul]; exact ENat.natCast_ne_top _) hb
  rw [← ENat.natCast_toNat hf,← Nat.cast_pow,← Nat.cast_mul] at hb
  have hb' : ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) ≤
      (C : ℝ)*(q : ℝ)^(Lech.dimension R-1) := by exact_mod_cast hb
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ ((C : ℝ)*(q : ℝ)^(Lech.dimension R-1))/(q : ℝ)^Lech.dimension R :=
      div_le_div_of_nonneg_right hb' (by positivity)
    _ = (C : ℝ)/q := by
      rw [show Lech.dimension R = (Lech.dimension R-1)+1 from by omega,
        pow_succ]
      field_simp
      simp only [Nat.add_sub_cancel]

theorem normalized_error_tendsto (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := normalized_error_bound H hH hg
  apply squeeze_zero' (Eventually.of_forall (fun q => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => hC q hq))
  simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
    Tendsto (fun q : ℕ => (C : ℝ)/(q : ℝ)) atTop (𝓝 0))

end Lech.FrobeniusGrowth


namespace Lech.FrobeniusGrowth
open Filter
open scoped ENNReal Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma normalized_error_tendstoENNReal (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ => ((q : ℝ≥0∞)^Lech.dimension R)⁻¹ *
      (Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g}))).toENNReal)
      atTop (𝓝 0) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (normalized_error_tendsto H hH hg)
  simp only [Function.comp_def,ENNReal.ofReal_zero] at ht
  apply ht.congr'
  obtain ⟨C,hC⟩ := quotient_colength_bound H hH hg
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hf : Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [← Nat.cast_pow,← Nat.cast_mul]; exact ENat.natCast_ne_top _) (hC q hq)
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]
  congr 1
  exact congrArg ENat.toENNReal (ENat.natCast_toNat hf)

lemma frobenius_error_tendstoENNReal (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰)
    (p : ℕ) [Fact p.Prime] [CharP R p] :
    Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension R))⁻¹ *
      (Module.length R (R ⧸ (H.map (iterateFrobenius R p n) ⊔ Ideal.span {g}))).toENNReal)
      atTop (𝓝 0) := by
  have ht := (normalized_error_tendstoENNReal H hH hg).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by exact (Fact.out : p.Prime).one_lt))
  apply ht.congr
  intro n
  dsimp only [Function.comp_def]
  rw [powerIdeal_eq_map H p n]
  simp only [Nat.cast_pow,← pow_mul]
end Lech.FrobeniusGrowth


namespace Lech.RootTower
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma perfectClosure_flat : (PerfectClosure.of (MvPowerSeries σ k) p).Flat := by
  let A := MvPowerSeries σ k
  have hf : (algebraMap (rootRing A p 0) (PerfectClosure A p)).Flat := by
    apply RingHom.flat_algebraMap_iff.mpr
    exact (regularTower σ k p).flat_limit 0
  have h := (RingHom.Flat.of_bijective (rootEquiv A p 0).bijective).comp hf
  have he : (algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
      (rootEquiv A p 0).toRingHom = PerfectClosure.of A p := by
    apply DFunLike.ext
    intro a
    rfl
  change ((algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
    (rootEquiv A p 0).toRingHom).Flat at h
  rwa [he] at h
end Lech.RootTower


namespace Lech.PerfectDomainStages
open Lech.RootTower Filter
open scoped ENNReal Topology nonZeroDivisors
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
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

local instance : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem frobenius_colength_tendsto
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (H : Ideal D) (hH : H.radical = IsLocalRing.maximalIdeal D) :
    Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
      atTop (𝓝 (normalizedLength (Fin h) k p
        ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
  let A := MvPowerSeries (Fin h) k
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hi (n : ℕ) := tensorMap_injective A D p L K hflat n
  have hdim : Lech.dimension D = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A D)
      (Algebra.IsIntegral.isIntegral : (algebraMap A D).IsIntegral) hf
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast D
    rw [hd] at hh
    exact_mod_cast hh
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  have hgn : algebraMap A D g ∈ D⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr
    (fun hz => hg (hf (by simpa using hz)))
  have herr := Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal H hH hgn p
  rw [hdim] at herr
  have hfinite (n : ℕ) :
      normalizedLength (Fin h) k p ((stage A D p n) ⧸ H.map (originalToStage A D p n)) ≠ ⊤ := by
    rw [normalizedLength_actual_stage_quotient (Fin h) k D p hres H n (hi n)]
    obtain ⟨c,hc⟩ := Lech.FrobeniusGrowth.linear_power_containment H hH
    have hl := Lech.length_quotient_le D (hc (p^n) (Nat.one_le_pow n p (Fact.out : p.Prime).pos))
    have hlfin := ne_top_of_le_ne_top (Lech.quotient_length_ne_top D (c*p^n)) hl
    rw [Lech.FrobeniusGrowth.powerIdeal_eq_map H p n] at hlfin
    apply ENNReal.mul_ne_top
    · apply ENNReal.inv_ne_top.mpr
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · simpa using hlfin
  have ht := Lech.SubalgebraStage.quotient_length_tendsto (stage A D p) (PerfectClosure.of D p)
    (original_mem_stage A D p) (regularTower (Fin h) k p) H (stage_mono A D p)
    (stage_exhaustive A D p) (fun n => rootMap A p n g) hgc hfinite ?_
  · apply ht.congr
    intro n
    change normalizedLength (Fin h) k p ((stage A D p n) ⧸
      H.map (originalToStage A D p n)) = _
    simpa only [Fintype.card_fin] using
      normalizedLength_actual_stage_quotient (Fin h) k D p hres H n (hi n)
  · change Tendsto (fun n => normalizedLength (Fin h) k p ((stage A D p n) ⧸
        (H.map (originalToStage A D p n) ⊔ Ideal.span {algebraMap (PerfectClosure A p) _
          (rootMap A p n g)}))) atTop (𝓝 0)
    apply herr.congr
    intro n
    symm
    simpa only [Fintype.card_fin] using
      normalizedLength_scalar_stage_quotient (Fin h) k D p hres H n (hi n) g
end Lech.PerfectDomainStages
end
end

end OAI
