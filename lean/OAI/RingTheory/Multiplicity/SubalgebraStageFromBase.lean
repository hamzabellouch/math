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
namespace Lech.SubalgebraStage
variable {R D C : Type*} [CommRing R] [CommRing D] [CommRing C] [Algebra R C]
  (B : ℕ → Subalgebra R C) (f : D →+* C)
  (hf : ∀ n d, f d ∈ B n)

def fromBase (n : ℕ) : D →+* B n := f.codRestrict (B n).toSubring (hf n)

def ideal (H : Ideal D) (n : ℕ) : Ideal (B n) := H.map (fromBase B f hf n)

lemma ideal_map (H : Ideal D) (n : ℕ) :
    (ideal B f hf H n).map (algebraMap (B n) C) = H.map f := by
  rw [ideal,Ideal.map_map]
  rfl

def quotientMap (H : Ideal D) (n : ℕ) :
    ((B n) ⧸ ideal B f hf H n) →ₐ[R] C ⧸ H.map f :=
  Ideal.quotientMapₐ (H.map f) (B n).val (by
    rw [← Ideal.map_le_iff_le_comap]
    change (ideal B f hf H n).map (algebraMap (B n) C) ≤ _
    rw [ideal_map])

lemma quotientMap_ranges_mono (H : Ideal D) (hm : Monotone B) :
    Monotone (fun n => (quotientMap B f hf H n).toLinearMap.range) := by
  intro n m hnm y hy
  obtain ⟨x,rfl⟩ := hy
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk (ideal B f hf H m) ⟨b,hm hnm b.property⟩,rfl⟩

lemma quotientMap_ranges_exhaustive (H : Ideal D)
    (hex : ∀ c : C, ∃ n, c ∈ B n) :
    ∀ x : C ⧸ H.map f, ∃ n, x ∈ (quotientMap B f hf H n).toLinearMap.range := by
  intro x
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n,hc⟩ := hex c
  exact ⟨n,Ideal.Quotient.mk (ideal B f hf H n) ⟨c,hc⟩,rfl⟩

lemma quotientMap_kernel_killed (H : Ideal D) (n : ℕ) (g : R)
    (hg : ∀ c : C, g • c ∈ B n)
    (x : (quotientMap B f hf H n).toLinearMap.ker) : g • x = 0 := by
  apply Subtype.ext
  have h := Lech.Conductor.quotient_ideal_kernel_killed (B n) g hg (ideal B f hf H n) x
  apply h
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective (x : (B n) ⧸ ideal B f hf H n)
  have hx := x.property
  rw [← hb] at hx ⊢
  change Ideal.Quotient.mk _ (b : C) = 0 at hx ⊢
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [ideal_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

open Filter
open scoped Topology
 

theorem quotient_length_tendsto (T : Lech.NormalizedLength.Tower R)
    (H : Ideal D) (hm : Monotone B) (hex : ∀ c : C, ∃ n, c ∈ B n)
    (g : ℕ → R) (hg : ∀ n c, g n • c ∈ B n)
    (hfinite : ∀ n, T.length ((B n) ⧸ ideal B f hf H n) ≠ ⊤)
    (herr : Tendsto (fun n => T.length ((B n) ⧸
      (ideal B f hf H n ⊔ Ideal.span {algebraMap R (B n) (g n)}))) atTop (𝓝 0)) :
    Tendsto (fun n => T.length ((B n) ⧸ ideal B f hf H n))
      atTop (𝓝 (T.length (C ⧸ H.map f))) := by
  apply T.length_stage_tendsto (fun n => (B n) ⧸ ideal B f hf H n)
    (fun n => (quotientMap B f hf H n).toLinearMap)
    (quotientMap_ranges_mono B f hf H hm) (quotientMap_ranges_exhaustive B f hf H hex)
    _ herr
  intro n
  let F := (quotientMap B f hf H n).toLinearMap
  have h := T.length_torsion_subquotient_le F.ker.subtype (LinearMap.id : F.ker →ₗ[R] F.ker)
    (Submodule.subtype_injective _) Function.surjective_id (g n)
    (quotientMap_kernel_killed B f hf H n (g n) (hg n)) (hfinite n)
  rwa [T.length_scalar_cokernel] at h
end Lech.SubalgebraStage

open scoped nonZeroDivisors
namespace Lech.RootTower

lemma flat_colon_membership {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (a b : R) (c d : S)
    (h : f a * c = f b * d) :
    c ∈ ((Ideal.span ({b} : Set R)).colon {a}).map f := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : ∑ i : Fin 2, (![a,-b] i) • (![c,d] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_neg, neg_mul]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr h
  obtain ⟨k,u,v,hu,hr⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S) hh
  rw [show c = ∑ j, u 0 j • v j from hu 0]
  apply Ideal.sum_mem
  intro j _
  have hj : u 0 j ∈ (Ideal.span ({b} : Set R)).colon {a} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
    have hj := hr j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul] at hj
    refine ⟨u 1 j, ?_⟩
    have he : a * u 0 j = b * u 1 j := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hj)
    simpa only [mul_comm] using he
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hj)

lemma Frobenius_map_le_pow {R : Type*} [CommRing R] (p n : ℕ) [Fact p.Prime]
    [CharP R p] (I : Ideal R) :
    I.map (iterateFrobenius R p n) ≤ I ^ (p^n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change iterateFrobenius R p n x ∈ I ^ (p^n)
  rw [iterateFrobenius_def]
  exact Ideal.pow_mem_pow hx _

lemma integral_uniform_denominator {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {x : K} (hx : IsIntegral R x) :
    ∃ c : R, c ≠ 0 ∧ ∀ n : ℕ, IsLocalization.IsInteger R (c • x^n) := by
  obtain ⟨s,hs⟩ := hx.fg_adjoin_singleton
  obtain ⟨c,hc⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) s
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, fun n => ?_⟩
  have hn : x^n ∈ Submodule.span R (s : Set K) := by
    rw [hs]
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) n
  have hall : ∀ y ∈ Submodule.span R (s : Set K),
      IsLocalization.IsInteger R ((c : R) • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using (IsLocalization.isInteger_zero (R := R) (S := K))
    | add y z _ _ hy hz => simpa [smul_add] using IsLocalization.isInteger_add hy hz
    | smul a y _ hy =>
        rw [smul_comm]
        exact IsLocalization.isInteger_smul hy
  exact hall _ hn

 

theorem isIntegrallyClosed_of_flat_frobenius (R : Type*) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hf : ∀ n, (iterateFrobenius R p n).Flat) : IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨c,hc,hcx⟩ := integral_uniform_denominator hx
  obtain ⟨b,a,ha⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) x
  by_contra hn
  let J := (Ideal.span ({(b : R)} : Set R)).colon {a}
  have hJ : J ≠ ⊤ := by
    intro hJ
    have haJ : a ∈ Ideal.span ({(b : R)} : Set R) := by
      have h1 : (1 : R) ∈ J := hJ ▸ (show (1 : R) ∈ (⊤ : Ideal R) from trivial)
      simpa [J, Submodule.mem_colon_singleton] using h1
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp haJ
    apply hn
    refine ⟨y, ?_⟩
    apply mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property)
    rw [← map_mul, ← hy]
    simpa only [Algebra.smul_def] using ha
  have hcpow (n : ℕ) : c ∈ J ^ (p^n) := by
    obtain ⟨d,hd⟩ := hcx (p^n)
    simp only [Algebra.smul_def] at hd
    have he : (iterateFrobenius R p n) a * c =
        (iterateFrobenius R p n) (b : R) * d := by
      apply IsFractionRing.injective R (FractionRing R)
      simp only [map_mul, iterateFrobenius_def, map_pow]
      change (algebraMap R (FractionRing R) a)^(p^n) * algebraMap R (FractionRing R) c = _
      rw [ha]
      simp only [Algebra.smul_def, mul_pow]
      rw [mul_assoc, mul_comm (x^(p^n)), ← hd]
    exact Frobenius_map_le_pow p n J
      (flat_colon_membership (iterateFrobenius R p n) (hf n) a b c d he)
  apply hc
  apply (Ideal.mem_bot.mp : c ∈ (⊥ : Ideal R) → c = 0)
  rw [← J.iInf_pow_eq_bot_of_isDomain hJ]
  apply Ideal.mem_iInf.mpr
  intro n
  exact Ideal.pow_le_pow_right (by
    exact Nat.le_of_lt (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out))) (hcpow n)

end Lech.RootTower


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma exists_positive {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, 0 < d i := by
  by_contra h
  push Not at h
  apply hd
  ext i
  exact Nat.eq_zero_of_le_zero (h i)

def pick (d : σ →₀ ℕ) : Option σ :=
  if h : d = 0 then none else some (Classical.choose (exists_positive h))

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

def divide (f : MvPowerSeries σ R) (i : σ) : MvPowerSeries σ R :=
  fun d => if pick (d + Finsupp.single i 1) = some i then coeff (d + Finsupp.single i 1) f else 0

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


namespace Lech.Normalization
variable {R S : Type*} [CommRing R] [CommRing S]

 
lemma dimension_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under hpq

 
lemma injective_of_integral_dimension [IsDomain R] (f : R →+* S) (hf : f.IsIntegral)
    {h : ℕ} (hS : (h : WithBot ℕ∞) ≤ ringKrullDim S) (hR : ringKrullDim R ≤ h) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro r hr
  by_contra hn
  have hd := dimension_le_of_integral f.kerLift hf.kerLift
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hh : (h : WithBot ℕ∞) + 1 ≤ h :=
    (add_le_add (hS.trans hd) le_rfl).trans (hdrop.trans hR)
  norm_cast at hh
  omega

end Lech.Normalization


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech
variable {R S : Type*} [CommRing R] [CommRing S]
lemma ringKrullDim_eq_of_integral_injective (f : R →+* S)
    (hint : f.IsIntegral) (hf : Function.Injective f) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hint⟩
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  · apply iSup_le
    intro l
    obtain ⟨P,_,hP,hPP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
      (by rw [Ideal.under_def,← RingHom.ker_eq_comap_bot]
          change RingHom.ker f ≤ _
          rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
          exact bot_le)
    have : P.LiesOver l.head.asIdeal := (Ideal.liesOver_iff _ _).mpr hPP.symm
    obtain ⟨L,hL,_,_⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    simpa only [hL,ringKrullDim] using Order.LTSeries.length_le_krullDim L
end Lech


namespace Lech

noncomputable def dimension (A : Type*) [CommRing A] : ℕ :=
  (WithBot.unbotD 0 (ringKrullDim A)).toNat

noncomputable def colength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℕ :=
  (Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N)).toNat

noncomputable def normalizedColength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℝ :=
  (Nat.factorial (dimension A) : ℝ) * (colength A N : ℝ) /
    (N : ℝ) ^ dimension A

noncomputable def multiplicity (A : Type*) [CommRing A] [IsLocalRing A] : ℝ :=
  Filter.limUnder Filter.atTop (normalizedColength A)

 

theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))

 

theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top

 
theorem colength_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    (colength A N : ℕ∞) = Module.length A (A ⧸ (IsLocalRing.maximalIdeal A)^N) :=
  ENat.natCast_toNat (quotient_length_ne_top A N)

end Lech
end
end

end OAI
