import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits

open scoped BigOperators
open Filter Polynomial

namespace HahnWilson.Interpolation
variable {k : Type*} [Field k]

def budget (N : ℕ → ℕ) (m : ℕ) : ℕ := ∑' l : ℕ, m / N (l + 1)

def denominator (u : ℕ → PowerSeries k) (m i : ℕ) : PowerSeries k :=
  ∏ j ∈ (Finset.range (m + 1)).erase i, (u i - u j)

def coefficient (u : ℕ → PowerSeries k) (N : ℕ → ℕ) (m i : ℕ) : LaurentSeries k :=
  (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ budget N m /
    algebraMap (PowerSeries k) (LaurentSeries k) (denominator u m i)

def moment (u : ℕ → PowerSeries k) (N : ℕ → ℕ) (m n : ℕ) : LaurentSeries k :=
  ∑ i ∈ Finset.range (m + 1), coefficient u N m i *
    (algebraMap (PowerSeries k) (LaurentSeries k) (u i)) ^ n

def InPowerIdeal (r : ℕ) (f : LaurentSeries k) : Prop :=
  ∃ g : PowerSeries k, f =
    algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X ^ r * g)

def BalancedDistances (u : ℕ → PowerSeries k) (N : ℕ → ℕ) : Prop :=
  ∀ i j l : ℕ, 0 < l →
    ((l : ℕ∞) ≤ (PowerSeries.order (u i - u j)) ↔ i % N l = j % N l)

lemma residue_count_le (m i n : ℕ) (_hn : 0 < n) :
    ((Finset.range (m + 1)).filter fun j => j % n = i % n).card ≤ m / n + 1 := by
  let s := (Finset.range (m + 1)).filter fun j => j % n = i % n
  have hinj : Set.InjOn (fun j : ℕ => j / n) s := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    change a / n = b / n at hab
    calc
      a = a % n + n * (a / n) := (Nat.mod_add_div a n).symm
      _ = b % n + n * (b / n) := by rw [ha', hb', hab]
      _ = b := Nat.mod_add_div b n
  calc
    s.card = (s.image (fun j => j / n)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (m / n + 1)).card := Finset.card_le_card (by
      intro j hj
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
      have ham : a ≤ m := by have := (Finset.mem_filter.mp ha).1; simpa using this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ham)))
    _ = m / n + 1 := Finset.card_range _

lemma residue_others_count_le (m i n : ℕ) (hn : 0 < n) (hi : i ≤ m) :
    (((Finset.range (m + 1)).erase i).filter fun j => j % n = i % n).card ≤ m / n := by
  have he : ((Finset.range (m + 1)).erase i).filter (fun j => j % n = i % n) =
      ((Finset.range (m + 1)).filter (fun j => j % n = i % n)).erase i := by
    ext j; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [he, Finset.card_erase_of_mem (by simp [hi])]
  simpa using Nat.sub_le_sub_right (residue_count_le m i n hn) 1

lemma budget_finite_support (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop) (m : ℕ) :
    (Function.support (fun l : ℕ => m / N (l + 1))).Finite := by
  obtain ⟨b,hb⟩ := (eventually_atTop.mp ((tendsto_atTop.1 hNt) (m + 1)))
  refine Set.Finite.subset (Set.finite_Iio b) ?_
  intro l hl
  change l < b
  apply lt_of_not_ge
  intro hbl
  have hlt : m < N (l + 1) := by have := hb (l + 1) (by omega); omega
  exact hl (Nat.div_eq_of_lt hlt)

lemma sum_power_div_denominator_integral
    {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (u : ℕ → R) (m n : ℕ)
    (hu : Set.InjOn (fun i => f (u i)) (Finset.range (m + 1))) :
    ∃ c : R, (∑ i ∈ Finset.range (m + 1),
      (f (u i)) ^ n / ∏ j ∈ (Finset.range (m + 1)).erase i, (f (u i) - f (u j))) = f c := by
  let P : Polynomial R := ∏ i ∈ Finset.range (m + 1), (X - C (u i))
  let Q : Polynomial R := X ^ n %ₘ P
  have hP : P.Monic := monic_prod_X_sub_C u _
  have hPK : (P.map f).degree = ((m + 1 : ℕ) : WithBot ℕ) := by
    simp [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      degree_prod, degree_X_sub_C]
  have hQ : (Q.map f).degree < ((Finset.range (m + 1)).card : WithBot ℕ) := by
    rw [show Q.map f = (X ^ n : Polynomial K) %ₘ P.map f by
      simp [Q, Polynomial.map_modByMonic f hP]]
    simpa [hPK] using Polynomial.degree_modByMonic_lt (X ^ n : Polynomial K) (hP.map f)
  have hev (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      (Q.map f).eval (f (u i)) = (f (u i)) ^ n := by
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ f (f (u i)) (X ^ n %ₘ P) = _
    rw [Polynomial.eval₂_modByMonic_eq_self_of_root]
    · simp
    · simp only [P, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact Finset.prod_eq_zero hi (sub_self _)
  refine ⟨Q.coeff m, ?_⟩
  have hc := Lagrange.coeff_eq_sum hu hQ
  calc
    _ = ∑ i ∈ Finset.range (m + 1), (Q.map f).eval (f (u i)) /
        ∏ j ∈ (Finset.range (m + 1)).erase i, (f (u i) - f (u j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hev i hi]
    _ = f (Q.coeff m) := by
      simpa only [Finset.card_range, Nat.add_sub_cancel, Polynomial.coeff_map] using hc.symm

lemma sum_eq_level_counts {ι : Type*} (s : Finset ι) (v : ι → ℕ) (L : ℕ)
    (hv : ∀ i ∈ s, v i ≤ L) :
    (∑ i ∈ s, v i) = ∑ l ∈ Finset.range L, (s.filter fun i => l < v i).card := by
  classical
  have hcount (i : ι) (hi : i ∈ s) :
      v i = ∑ l ∈ Finset.range L, if l < v i then 1 else 0 := by
    have he : (Finset.range L).filter (fun l => l < v i) = Finset.range (v i) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (hv i hi), h⟩⟩
    rw [← Finset.card_filter, he, Finset.card_range]
  calc
    _ = ∑ i ∈ s, ∑ l ∈ Finset.range L, if l < v i then 1 else 0 := Finset.sum_congr rfl hcount
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.card_filter]

lemma denominator_ne_zero (u : ℕ → PowerSeries k) (hu : Function.Injective u)
    (m i : ℕ) : denominator u m i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hu he).symm)

lemma denominator_order_le (u : ℕ → PowerSeries k) (N : ℕ → ℕ)
    (hu : Function.Injective u) (hN : ∀ l, 0 < l → 0 < N l)
    (hNt : Tendsto N atTop atTop) (hbal : BalancedDistances u N)
    (m i : ℕ) (hi : i ≤ m) :
    (PowerSeries.order (denominator u m i)) ≤ (budget N m : ℕ∞) := by
  let s := (Finset.range (m + 1)).erase i
  let v : ℕ → ℕ := fun j => (PowerSeries.order (u i - u j)).toNat
  have hfin (j : ℕ) (hj : j ∈ s) : (PowerSeries.order (u i - u j)) ≠ ⊤ := by
    exact PowerSeries.order_eq_top.not.mpr
      (sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hu he).symm))
  have hlevels (l : ℕ) :
      s.filter (fun j => l < v j) = s.filter (fun j => j % N (l + 1) = i % N (l + 1)) := by
    apply Finset.filter_congr
    intro j hj
    have ht : l < v j ↔ ((l + 1 : ℕ) : ℕ∞) ≤ (PowerSeries.order (u i - u j)) := by
      rw [← ENat.natCast_toNat (hfin j hj)]
      norm_cast
    rw [ht, hbal i j (l + 1) (by omega), eq_comm]
  have hb : (∑ j ∈ s, v j) ≤ budget N m := by
    let L := ∑ j ∈ s, v j
    rw [sum_eq_level_counts s v L (fun j hj => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj)]
    have hsum : Summable (fun l : ℕ => m / N (l + 1)) :=
      summable_of_hasFiniteSupport (budget_finite_support N hNt m)
    apply le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (hsum.sum_le_tsum (Finset.range L) (fun _ _ => Nat.zero_le _))
    rw [hlevels]
    exact residue_others_count_le m i (N (l + 1)) (hN _ (by omega)) hi
  calc
    (PowerSeries.order (denominator u m i)) = ∑ j ∈ s, (PowerSeries.order (u i - u j)) := PowerSeries.order_prod _ _
    _ = ((∑ j ∈ s, v j : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun j hj => (ENat.natCast_toNat (hfin j hj)).symm)
    _ ≤ _ := by exact_mod_cast hb

lemma quotient_X_pow_integral (d : PowerSeries k) (hd : d ≠ 0) (r : ℕ)
    (hr : PowerSeries.order d ≤ (r : ℕ∞)) :
    InPowerIdeal 0
      ((algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ r /
        algebraMap (PowerSeries k) (LaurentSeries k) d) := by
  let e := (PowerSeries.order d).toNat
  have he : e ≤ r := ENat.toNat_le_of_le_natCast hr
  let v := PowerSeries.Inv_divided_by_X_pow_order hd
  have hdv : d * (PowerSeries.X ^ (r - e) * v) = PowerSeries.X ^ r := by
    conv_lhs => lhs; rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := d)]
    calc
      PowerSeries.X ^ e * d.divXPowOrder * (PowerSeries.X ^ (r - e) * v) =
          (PowerSeries.X ^ e * PowerSeries.X ^ (r - e)) * (d.divXPowOrder * v) := by ring
      _ = PowerSeries.X ^ r := by
        rw [PowerSeries.Inv_divided_by_X_pow_order_rightInv hd, mul_one, ← pow_add,
          Nat.add_sub_of_le he]
  refine ⟨PowerSeries.X ^ (r - e) * v, ?_⟩
  have hdm : algebraMap (PowerSeries k) (LaurentSeries k) d ≠ 0 :=
    (map_ne_zero_iff (algebraMap (PowerSeries k) (LaurentSeries k))
      (IsFractionRing.injective (PowerSeries k) (LaurentSeries k))).mpr hd
  simp only [pow_zero, one_mul]
  apply (div_eq_iff hdm).mpr
  have heq := congrArg (algebraMap (PowerSeries k) (LaurentSeries k)) hdv
  simpa only [map_mul, map_pow, mul_comm] using heq.symm

lemma coefficient_integral (u : ℕ → PowerSeries k) (N : ℕ → ℕ)
    (hu : Function.Injective u) (hN : ∀ l, 0 < l → 0 < N l)
    (hNt : Tendsto N atTop atTop) (hbal : BalancedDistances u N)
    (m i : ℕ) (hi : i ≤ m) : InPowerIdeal 0 (coefficient u N m i) :=
  quotient_X_pow_integral _ (denominator_ne_zero u hu m i) _
    (denominator_order_le u N hu hN hNt hbal m i hi)

lemma sum_power_div_denominator_small {K : Type*} [Field K]
    (u : ℕ → K) (m n : ℕ)
    (hu : Set.InjOn u (Finset.range (m + 1))) (hn : n ≤ m) :
    (∑ i ∈ Finset.range (m + 1),
      (u i) ^ n / ∏ j ∈ (Finset.range (m + 1)).erase i, (u i - u j)) =
      if n = m then 1 else 0 := by
  have hp : (X ^ n : Polynomial K).degree <
      ((Finset.range (m + 1)).card : WithBot ℕ) := by
    simp only [Polynomial.degree_X_pow, Finset.card_range, Nat.cast_lt]
    exact Nat.lt_succ_of_le hn
  have hc := Lagrange.coeff_eq_sum hu hp
  simpa only [Finset.card_range, Nat.add_sub_cancel, Polynomial.coeff_X_pow,
    Polynomial.eval_pow, Polynomial.eval_X, eq_comm] using hc.symm

lemma moment_eq (u : ℕ → PowerSeries k) (N : ℕ → ℕ) (m n : ℕ) :
    moment u N m n =
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ budget N m *
      ∑ i ∈ Finset.range (m + 1),
        (algebraMap (PowerSeries k) (LaurentSeries k) (u i)) ^ n /
        ∏ j ∈ (Finset.range (m + 1)).erase i,
          (algebraMap (PowerSeries k) (LaurentSeries k) (u i) -
           algebraMap (PowerSeries k) (LaurentSeries k) (u j)) := by
  simp only [moment, coefficient, denominator, map_prod, map_sub, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => by simp only [div_eq_mul_inv]; ring)

lemma moment_small (u : ℕ → PowerSeries k) (N : ℕ → ℕ)
    (hu : Function.Injective u) (m n : ℕ) (hn : n ≤ m) :
    moment u N m n =
      if n = m then (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ budget N m
      else 0 := by
  rw [moment_eq, sum_power_div_denominator_small
    (fun i => algebraMap (PowerSeries k) (LaurentSeries k) (u i)) m n
    ((IsFractionRing.injective (PowerSeries k) (LaurentSeries k)).comp hu).injOn hn]
  split_ifs <;> simp

lemma sum_power_div_denominator_scale {K : Type*} [Field K]
    (v : ℕ → K) (x : K) (hx : x ≠ 0) (m n : ℕ) (hmn : m ≤ n) :
    (∑ i ∈ Finset.range (m + 1),
      (x * v i) ^ n / ∏ j ∈ (Finset.range (m + 1)).erase i, (x * v i - x * v j)) =
    x ^ (n - m) * (∑ i ∈ Finset.range (m + 1),
      (v i) ^ n / ∏ j ∈ (Finset.range (m + 1)).erase i, (v i - v j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : ((Finset.range (m + 1)).erase i).card = m := by
    rw [Finset.card_erase_of_mem hi, Finset.card_range, Nat.add_sub_cancel]
  simp only [← mul_sub, Finset.prod_mul_distrib, Finset.prod_const, hcard, mul_pow]
  rw [← div_mul_div_comm, pow_sub₀ x hx hmn]
  simp only [div_eq_mul_inv]

lemma moment_large (u : ℕ → PowerSeries k) (N : ℕ → ℕ)
    (hu : Function.Injective u) (hu0 : ∀ i, PowerSeries.constantCoeff (u i) = 0)
    (m n : ℕ) (hmn : m ≤ n) :
    InPowerIdeal (budget N m + n - m) (moment u N m n) := by
  have hdiv (i : ℕ) : PowerSeries.X ∣ u i := PowerSeries.X_dvd_iff.mpr (hu0 i)
  choose v hv using hdiv
  let f := algebraMap (PowerSeries k) (LaurentSeries k)
  have hf : Function.Injective f := IsFractionRing.injective (PowerSeries k) (LaurentSeries k)
  have hvf : Function.Injective (fun i => f (v i)) := by
    intro i j hij
    apply hu
    rw [hv i, hv j, hf hij]
  obtain ⟨c,hc⟩ := sum_power_div_denominator_integral f v m n hvf.injOn
  have hx : f PowerSeries.X ≠ 0 := (map_ne_zero_iff f hf).mpr PowerSeries.X_ne_zero
  have huf (i : ℕ) : f (u i) = f PowerSeries.X * f (v i) := by rw [hv i, map_mul]
  refine ⟨c, ?_⟩
  rw [moment_eq]
  change f PowerSeries.X ^ budget N m *
    (∑ i ∈ Finset.range (m + 1), f (u i) ^ n /
      ∏ j ∈ (Finset.range (m + 1)).erase i, (f (u i) - f (u j))) = _
  simp only [huf]
  rw [sum_power_div_denominator_scale (fun i => f (v i)) (f PowerSeries.X) hx m n hmn, hc]
  simp only [map_mul, map_pow]
  rw [← mul_assoc, ← pow_add, show budget N m + (n - m) = budget N m + n - m by omega]

theorem integral_divided_differences
    (u : ℕ → PowerSeries k) (N : ℕ → ℕ)
    (hu : Function.Injective u) (hu0 : ∀ i, PowerSeries.constantCoeff (u i) = 0)
    (hN : ∀ l, 0 < l → 0 < N l) (hNt : Tendsto N atTop atTop)
    (hbal : BalancedDistances u N) (m : ℕ) :
    (∀ i ≤ m, InPowerIdeal 0 (coefficient u N m i)) ∧
    (∀ n < m, moment u N m n = 0) ∧
    moment u N m m =
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ budget N m ∧
    (∀ n, m < n → InPowerIdeal (budget N m + n - m) (moment u N m n)) := by
  refine ⟨fun i hi => coefficient_integral u N hu hN hNt hbal m i hi, ?_, ?_, ?_⟩
  · intro n hn
    simpa [ne_of_lt hn] using moment_small u N hu m n hn.le
  · simpa using moment_small u N hu m m le_rfl
  · intro n hn
    exact moment_large u N hu hu0 m n hn.le

end HahnWilson.Interpolation

end

end OAI
