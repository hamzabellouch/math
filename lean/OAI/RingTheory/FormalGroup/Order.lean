import Mathlib
import OAI.RingTheory.FormalGroup.Endomorphism

namespace OAI

/-! Orders and linear coefficients of formal-group endomorphisms. -/

noncomputable section
namespace LowerFormalGroup
variable {K : Type*} [Field K]
lemma coeff_subst_zero_X (f : MvPowerSeries (Fin 2) K) (n : ℕ) :
    PowerSeries.coeff n (f.subst ![0, PowerSeries.X]) =
      f.coeff (Finsupp.single 1 n) := by
  have hb : MvPowerSeries.HasSubst ![0, (PowerSeries.X : PowerSeries K)] :=
    MvPowerSeries.HasSubst.zero_X
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hb,
    finsum_eq_single _ (Finsupp.single 1 n)]
  · simp
  · intro d hd
    by_cases h0 : d 0 = 0
    · have h1 : d 1 ≠ n := by
        intro hh
        apply hd
        ext i
        fin_cases i <;> simp_all
      simp [h0, PowerSeries.coeff_X_pow, Ne.symm h1]
    · simp [h0]

lemma formal_first_factor (F : FormalGroup K) :
    ∃ u : MvPowerSeries (Fin 2) K,
      F.toPowerSeries - MvPowerSeries.X 1 = MvPowerSeries.X 0 * u ∧
      u.constantCoeff = 1 := by
  have hd : MvPowerSeries.X 0 ∣ (F.toPowerSeries - MvPowerSeries.X 1) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro d h0
    have he : d = Finsupp.single 1 (d 1) := by
      ext i
      fin_cases i <;> simp_all
    have hc := congrArg (PowerSeries.coeff (d 1)) F.zeroX_eq_X
    rw [FormalGroup.zeroX, coeff_subst_zero_X] at hc
    rw [map_sub, he, hc]
    simp [PowerSeries.coeff_X, MvPowerSeries.coeff_X,
      (Finsupp.single_injective (1 : Fin 2)).eq_iff]
  obtain ⟨u, hu⟩ := hd
  refine ⟨u, hu, ?_⟩
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hu
  simpa [F.lin_coeff_X, MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h.symm

lemma mv_const_subst (a : Fin 2 → PowerSeries K) (ha : MvPowerSeries.HasSubst a)
    (ha0 : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (f : MvPowerSeries (Fin 2) K) :
    PowerSeries.constantCoeff (f.subst a) = f.constantCoeff := by
  have h0 : (f - MvPowerSeries.C f.constantCoeff).constantCoeff = 0 := by simp
  have h := MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 h0
  rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_C, map_sub,
    MvPowerSeries.constantCoeff_C] at h
  exact sub_eq_zero.mp h

lemma points_hasSubst {F : FormalGroup K} (x y : F.Point Unit) :
    MvPowerSeries.HasSubst ![x.val, y.val] := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
  intro i
  fin_cases i
  · exact x.prop
  · exact y.prop

lemma formal_point_factor {F : FormalGroup K} (x y : F.Point Unit) :
    ∃ u : PowerSeries K, (x + y).val - y.val = x.val * u ∧ u.constantCoeff = 1 := by
  obtain ⟨v, hv, hv0⟩ := formal_first_factor F
  have hxy := points_hasSubst x y
  refine ⟨v.subst ![x.val, y.val], ?_, ?_⟩
  · have h := congrArg (MvPowerSeries.subst ![x.val, y.val]) hv
    rw [MvPowerSeries.subst_sub hxy, MvPowerSeries.subst_X hxy,
      MvPowerSeries.subst_mul hxy, MvPowerSeries.subst_X hxy] at h
    exact h
  · rw [mv_const_subst _ hxy, hv0]
    intro i
    fin_cases i
    · exact point_const_zero x
    · exact point_const_zero y

lemma formal_point_order {F : FormalGroup K} (x y : F.Point Unit) :
    PowerSeries.order ((x + y).val - y.val) = PowerSeries.order x.val := by
  obtain ⟨u, hu, hu0⟩ := formal_point_factor x y
  have hord : u.order = 0 := by
    by_contra h
    exact one_ne_zero (hu0.symm.trans
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h))
  rw [hu, PowerSeries.order_mul, hord, add_zero]

lemma formal_point_coeff_one {F : FormalGroup K} (x y : F.Point Unit) :
    PowerSeries.coeff 1 (x + y).val = PowerSeries.coeff 1 x.val + PowerSeries.coeff 1 y.val := by
  obtain ⟨u, hu, hu0⟩ := formal_point_factor x y
  have h := congrArg (PowerSeries.coeff 1) hu
  rw [map_sub, PowerSeries.coeff_one_mul, point_const_zero x, hu0] at h
  simpa using (sub_eq_iff_eq_add.mp h)

lemma coeff_one_subst {f g : PowerSeries K} (hg : g.constantCoeff = 0) :
    PowerSeries.coeff 1 (f.subst g) = f.coeff 1 * g.coeff 1 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 1]
  · simp
  · intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have h : (1 : ℕ∞) < (g ^ n).order := by
      apply lt_of_lt_of_le _ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hg)
      exact_mod_cast (show 1 < n by omega)
    rw [PowerSeries.coeff_of_lt_order 1 h, smul_zero]

def naturalLinear {F : FormalGroup K} [F.IsComm] : naturalEnd F →+* K where
  toFun a := PowerSeries.coeff 1 (naturalSeries a)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := formal_point_coeff_one _ _
  map_mul' a b := by
    rw [naturalSeries_mul, coeff_one_subst (naturalSeries_constant_zero b)]

lemma naturalLinear_root_eq_one {F : FormalGroup K} [F.IsComm]
    (s : naturalEnd F) {p : ℕ} (hp : p.Prime) [CharP K p] (hsp : s ^ p = 1) :
    naturalLinear s = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  apply frobenius_inj K p
  change naturalLinear s ^ p = 1 ^ p
  rw [← map_pow, hsp, map_one, one_pow]

lemma naturalSeries_order_one {F : FormalGroup K} [F.IsComm]
    {a : naturalEnd F} (ha : naturalLinear a ≠ 0) :
    (naturalSeries a).order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨ha, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst i
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using naturalSeries_constant_zero a

lemma sum_powers_order_one {F : FormalGroup K} [F.IsComm]
    (s : naturalEnd F) {p : ℕ} (hp : p.Prime) [CharP K p] (hsp : s ^ p = 1)
    {j : ℕ} (hj : 0 < j) (hjp : j < p) :
    (naturalSeries (∑ i ∈ Finset.range j, s ^ i)).order = 1 := by
  apply naturalSeries_order_one
  simp only [map_sum, map_pow, naturalLinear_root_eq_one s hp hsp, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  intro hh
  exact (Nat.not_dvd_of_pos_of_lt hj hjp) ((CharP.cast_eq_zero_iff K p j).mp hh)

lemma naturalSeries_order_ne_zero {F : FormalGroup K} [F.IsComm]
    (a : naturalEnd F) : (naturalSeries a).order ≠ 0 := by
  exact PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr (naturalSeries_constant_zero a)

def naturalOrder {F : FormalGroup K} [F.IsComm] : naturalEnd F →* ℕ∞ where
  toFun a := (naturalSeries a).order
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · subst a
      simp only [zero_mul, naturalSeries_zero, PowerSeries.order_zero]
      exact (ENat.top_mul (naturalSeries_order_ne_zero b)).symm
    · rw [naturalSeries_mul]
      exact order_subst_nonzero (naturalSeries_eq_zero.not.mpr ha)
        (naturalSeries_constant_zero b)

lemma naturalSeries_natCast {F : FormalGroup K} [F.IsComm] (n : ℕ) :
    naturalSeries (n : naturalEnd F) = pSeries F n := by
  exact congrArg Subtype.val (AddMonoid.End.natCast_apply n (coordinate F))
end LowerFormalGroup
end

end OAI
