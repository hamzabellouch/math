import Mathlib
import OAI.RingTheory.FormalGroup.Order

namespace OAI

/-! Finite-height constraints and coordinate expansions for endomorphisms of prime order. -/

noncomputable section
namespace LowerFormalGroup
variable {K : Type*} [Field K]
section Torsion
variable {F : FormalGroup K} [F.IsComm] {p : ℕ} (hp : p.Prime)
    (s : naturalEnd F) (hsp : s ^ p = 1) (hs : s ≠ 1)

lemma formal_difference_order [CharP K p] (a b : naturalEnd F) :
    letI := naturalRing s hp.pos hsp hs
    (naturalSeries (a - b)).order = (naturalSeries a - naturalSeries b).order := by
  let := pointGroup s hp.pos hsp hs
  let := naturalRing s hp.pos hsp hs
  have h := formal_point_order ((a - b).val (coordinate F)) (b.val (coordinate F))
  have he : (a - b).val (coordinate F) + b.val (coordinate F) = a.val (coordinate F) := by
    exact congrArg (fun t : naturalEnd F => t.val (coordinate F)) (sub_add_cancel a b)
  rw [he] at h
  exact h.symm

variable [CharP K p]

lemma factor_power_order {j : ℕ} (hj : 0 < j) (hjp : j < p) :
    letI := naturalRing s hp.pos hsp hs
    naturalOrder (1 - s ^ j) = naturalOrder (1 - s) := by
  let := naturalRing s hp.pos hsp hs
  have fac : (1 - s) * (∑ i ∈ Finset.range j, s ^ i) = 1 - s ^ j := by
    have h := mul_geom_sum s j
    calc
      (1 - s) * (∑ i ∈ Finset.range j, s ^ i) =
          -((s - 1) * (∑ i ∈ Finset.range j, s ^ i)) := by rw [← neg_mul, neg_sub]
      _ = 1 - s ^ j := by rw [h, neg_sub]
  rw [← fac, map_mul]
  change _ * (naturalSeries (∑ i ∈ Finset.range j, s ^ i)).order = _
  rw [sum_powers_order_one s hp hsp hj hjp, mul_one]

open scoped IsMulCommutative in
lemma torsion_order_equation :
    letI := naturalRing s hp.pos hsp hs
    (naturalOrder (1 - s)) ^ (p - 1) = (pSeries F p).order := by
  let := naturalRing s hp.pos hsp hs
  have : IsDomain (naturalEnd F) := NoZeroDivisors.to_isDomain _
  let C := Subring.closure ({s} : Set (naturalEnd F))
  have : IsMulCommutative C :=
    Subring.isMulCommutative_closure (Set.pairwise_singleton s Commute)
  let μ : C := ⟨s, Subring.subset_closure (Set.mem_singleton s)⟩
  have hμp : μ ^ p = 1 := Subtype.ext hsp
  have hμne : μ ≠ 1 := fun h => hs (congrArg Subtype.val h)
  have hroot : IsPrimitiveRoot μ p := isPrimitiveRoot_of_mem_nthRootsFinset hp
    ((Polynomial.mem_nthRootsFinset hp.pos 1).mpr hμp) hμne
  have he := IsPrimitiveRoot.prod_one_sub_pow_eq_order
    (show IsPrimitiveRoot μ ((p - 1) + 1) by simpa [Nat.sub_add_cancel hp.one_le] using hroot)
  let o : C →* ℕ∞ := naturalOrder.comp C.subtype.toMonoidHom
  have heo := congrArg o he
  rw [map_prod] at heo
  have hfac : ∀ k ∈ Finset.range (p - 1), o (1 - μ ^ (k + 1)) = naturalOrder (1 - s) := by
    intro k hk
    exact factor_power_order hp s hsp hs (by omega) (by simp only [Finset.mem_range] at hk; omega)
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_range] at heo
  have hcast : o ((p - 1 : ℕ) + 1) = (pSeries F p).order := by
    change (naturalSeries ((p - 1 : ℕ) + 1 : naturalEnd F)).order = _
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le, naturalSeries_natCast]
  exact heo.trans hcast

lemma ordinary_difference_order (a : naturalEnd F) :
    letI := naturalRing s hp.pos hsp hs
    naturalOrder (1 - a) = (naturalSeries a - PowerSeries.X).order := by
  let := naturalRing s hp.pos hsp hs
  change (naturalSeries (1 - a)).order = _
  rw [formal_difference_order hp s hsp hs, naturalSeries_one,
    ← neg_sub (naturalSeries a), PowerSeries.order_neg]

include hp hsp hs in
lemma ordinary_order_equation :
    (naturalSeries s - PowerSeries.X).order ^ (p - 1) = (pSeries F p).order := by
  let := naturalRing s hp.pos hsp hs
  have h := torsion_order_equation hp s hsp hs
  rw [ordinary_difference_order hp s hsp hs] at h
  exact h

include hp hsp hs in
lemma ordinary_power_order {j : ℕ} (hj : 0 < j) (hjp : j < p) :
    (naturalSeries (s ^ j) - PowerSeries.X).order =
      (naturalSeries s - PowerSeries.X).order := by
  let := naturalRing s hp.pos hsp hs
  rw [← ordinary_difference_order hp s hsp hs,
      ← ordinary_difference_order hp s hsp hs]
  exact factor_power_order hp s hsp hs hj hjp

end Torsion

lemma height_divisibility_and_order {F : FormalGroup K} [F.IsComm]
    {p : ℕ} (hp : p.Prime) [CharP K p] (s : naturalEnd F) (hsp : s ^ p = 1)
    (hs : s ≠ 1) {m : ℕ} (height : (pSeries F p).order = (p ^ m : ℕ)) :
    (p - 1) ∣ m ∧ (m = p - 1 → (naturalSeries s - PowerSeries.X).order = (p : ℕ∞)) := by
  have hnonzero : naturalSeries s - PowerSeries.X ≠ 0 := by
    intro h
    apply hs
    apply naturalSeries_injective
    exact sub_eq_zero.mp h
  let n := (naturalSeries s - PowerSeries.X).order.toNat
  have hn : (naturalSeries s - PowerSeries.X).order = (n : ℕ∞) :=
    (PowerSeries.coe_toNat_order hnonzero).symm
  have he := ordinary_order_equation hp s hsp hs
  rw [height, hn, ← Nat.cast_pow] at he
  have heN : n ^ (p - 1) = p ^ m := by exact_mod_cast he
  have hfac := congrArg (fun a : ℕ => a.factorization p) heN
  simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    hp.factorization_self, mul_one] at hfac
  refine ⟨⟨n.factorization p, hfac.symm⟩, ?_⟩
  intro hm
  rw [hm] at heN
  have hnP : n = p := (Nat.pow_left_inj (by have := hp.two_le; omega)).mp heN
  rw [hn, hnP]

theorem order_p_finite_height
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) [CharP K p]
    (F : FormalGroup K) [F.IsComm] (σ : End F)
    (hσp : iterate σ.series p = PowerSeries.X)
    (hσne : σ.series ≠ PowerSeries.X)
    (m : ℕ) (hm : (pSeries F p).order = (↑(p ^ m) : ℕ∞)) :
    (p - 1) ∣ m ∧
      (m = p - 1 →
        (σ.series - PowerSeries.X).order = (p : ℕ∞) ∧
        (iterate σ.series (p - 1) - PowerSeries.X).order = (p : ℕ∞)) := by
  have hsp : σ.asNatural ^ p = 1 := by
    apply naturalSeries_injective
    rw [naturalSeries_pow_asNatural, hσp, naturalSeries_one]
  have hs : σ.asNatural ≠ 1 := by
    intro h
    apply hσne
    simpa only [naturalSeries_asNatural, naturalSeries_one] using congrArg naturalSeries h
  obtain ⟨hdiv, hord⟩ := height_divisibility_and_order hp σ.asNatural hsp hs hm
  refine ⟨hdiv, fun hheight => ?_⟩
  have hσord : (σ.series - PowerSeries.X).order = (p : ℕ∞) :=
    by simpa only [naturalSeries_asNatural] using hord hheight
  refine ⟨hσord, ?_⟩
  have hi := ordinary_power_order hp σ.asNatural hsp hs
    (j := p - 1) (by have := hp.two_le; omega) (by obtain ⟨half, hhalf⟩ := hodd; omega)
  rw [naturalSeries_pow_asNatural, naturalSeries_asNatural] at hi
  exact hi.trans hσord

lemma expansion_of_order {f : PowerSeries K} {p : ℕ}
    (h : (f - PowerSeries.X).order = (p : ℕ∞)) :
    ∃ c : K, c ≠ 0 ∧ ∃ r : PowerSeries K,
      f = PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ p +
        PowerSeries.X ^ (p + 1) * r := by
  let g := f - PowerSeries.X
  have ht : g.order.toNat = p := by rw [h, ENat.toNat_natCast]
  let c := g.divXPowOrder.constantCoeff
  have hc : c ≠ 0 := by
    dsimp only [c]
    rw [PowerSeries.constantCoeff_divXPowOrder, ht]
    exact (PowerSeries.order_eq_nat.mp h).1
  have hd : PowerSeries.X ∣ g.divXPowOrder - PowerSeries.C c := by
    apply PowerSeries.X_dvd_iff.mpr
    simp only [map_sub, PowerSeries.constantCoeff_C, c, sub_self]
  obtain ⟨r, hr⟩ := hd
  refine ⟨c, hc, r, ?_⟩
  have hf : PowerSeries.X ^ p * g.divXPowOrder = g := by
    rw [← ht, PowerSeries.X_pow_order_mul_divXPowOrder]
  have hv : g.divXPowOrder = PowerSeries.X * r + PowerSeries.C c :=
    sub_eq_iff_eq_add.mp hr
  calc
    f = PowerSeries.X + g := by dsimp [g]; ring
    _ = PowerSeries.X + PowerSeries.X ^ p * g.divXPowOrder := by rw [hf]
    _ = _ := by rw [hv, pow_succ]; ring

theorem order_p_finite_height_expansion
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) [CharP K p]
    (F : FormalGroup K) [F.IsComm] (σ : End F)
    (hσp : iterate σ.series p = PowerSeries.X)
    (hσne : σ.series ≠ PowerSeries.X)
    (m : ℕ) (hm : (pSeries F p).order = (↑(p ^ m) : ℕ∞)) :
    (p - 1) ∣ m ∧ (m = p - 1 →
      (∃ c : K, c ≠ 0 ∧ ∃ r : PowerSeries K,
        σ.series = PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ p +
          PowerSeries.X ^ (p + 1) * r) ∧
      (∃ c : K, c ≠ 0 ∧ ∃ r : PowerSeries K,
        iterate σ.series (p - 1) = PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ p +
          PowerSeries.X ^ (p + 1) * r)) := by
  obtain ⟨hd, ho⟩ := order_p_finite_height p hp hodd F σ hσp hσne m hm
  exact ⟨hd, fun hh => ⟨expansion_of_order (ho hh).1, expansion_of_order (ho hh).2⟩⟩

lemma iterate_inverse {F : FormalGroup K} [F.IsComm] (σ : End F)
    {p : ℕ} (hp : 0 < p) (hσp : iterate σ.series p = PowerSeries.X) :
    PowerSeries.subst σ.series (iterate σ.series (p - 1)) = PowerSeries.X ∧
    PowerSeries.subst (iterate σ.series (p - 1)) σ.series = PowerSeries.X := by
  have hsp : σ.asNatural ^ p = 1 := by
    apply naturalSeries_injective
    rw [naturalSeries_pow_asNatural, hσp, naturalSeries_one]
  have hp' : (p - 1) + 1 = p := by omega
  constructor
  · have h : σ.asNatural ^ (p - 1) * σ.asNatural = 1 := by
      rw [← pow_succ, hp', hsp]
    have hx := congrArg naturalSeries h
    simpa only [naturalSeries_mul, naturalSeries_pow_asNatural,
      naturalSeries_asNatural, naturalSeries_one] using hx
  · have h : σ.asNatural * σ.asNatural ^ (p - 1) = 1 := by
      rw [← pow_succ', hp', hsp]
    have hx := congrArg naturalSeries h
    simpa only [naturalSeries_mul, naturalSeries_pow_asNatural,
      naturalSeries_asNatural, naturalSeries_one] using hx

end LowerFormalGroup
end

end OAI
