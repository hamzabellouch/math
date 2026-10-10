import Mathlib
import OAI.RingTheory.Multiplicity.KoszulQuotientFinite

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma frobenius_quotient_homology_nat_bound
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R)
    (hI : (I ⊔ Koszul.entryIdeal zs).radical = IsLocalRing.maximalIdeal R) (i : ℤ) :
    ∃ C : ℕ, ∀ n,
      (Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat ≤ (p^n)^zs.length * C := by
  obtain ⟨a,ha,hbound⟩ := frobenius_quotient_homology_bound p F hF I zs hzs
  let L : ℕ∞ := ∑ k∈Finset.range (dimension R+1),
    Module.finrank R (F.X (-(dimension R : ℤ)+k)) • Module.length R
      ((Koszul.tensor (zs.map (fun z => z^a)) ((complexQuotient I (.up ℤ)).obj
        ((single (ModuleCat R) (.up ℤ) (-(dimension R : ℤ)+k)).obj
          (ModuleCat.of R R)))).homology i)
  have hL : L ≠ ⊤ := by
    apply ENat.sum_ne_top.mpr
    intro k hk
    have hf := Koszul.quotient_tensor_single_finiteLength I (zs.map (fun z => z^a))
      (by rw [Koszul.sup_entryIdeal_powers_radical I zs a ha]; exact hI)
      (-(dimension R:ℤ)+k) i
    have hl := Module.length_ne_top_iff.mpr hf
    rw [nsmul_eq_mul]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) hl
  refine ⟨L.toNat,fun n => ?_⟩
  have h := ENat.toNat_le_toNat (hbound n i)
    (show ((p^n)^zs.length) • L ≠ ⊤ by
      rw [nsmul_eq_mul]
      exact WithTop.mul_ne_top (ENat.natCast_ne_top _) hL)
  simpa only [nsmul_eq_mul,ENat.toNat_mul,ENat.toNat_natCast,L] using h

lemma tendsto_normalized_polynomial (p r d : ℕ) (hp : 1 < p) (hr : r < d) (C : ℝ) :
    Tendsto (fun n : ℕ => C * ((p:ℝ)^n)^r / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p:ℝ) := by positivity
  have hratio : 0 ≤ ((p:ℝ)^r / (p:ℝ)^d) := by positivity
  have hlt : (p:ℝ)^r / (p:ℝ)^d < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact pow_lt_pow_right₀ hp1 hr
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hlt).const_mul C
  convert ht using 1
  · ext n
    rw [div_pow,← pow_mul,← pow_mul]
    simp only [Nat.mul_comm n, pow_mul]
    ring
  · simp

 

theorem frobenius_quotient_homology_tendsto_zero
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R)
    (hI : (I ⊔ Koszul.entryIdeal zs).radical = IsLocalRing.maximalIdeal R)
    (hd : zs.length < dimension R) (i : ℤ) :
    Tendsto (fun n : ℕ =>
      ((Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat : ℝ) /
          ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0) := by
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  obtain ⟨C,hC⟩ := frobenius_quotient_homology_nat_bound p F hF I zs hzs hI i
  apply squeeze_zero
  · intro n; positivity
  · intro n
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have hc : ((Module.length R (((complexQuotient I (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i)).toNat : ℝ) ≤
        (((p^n)^zs.length * C : ℕ):ℝ) := by exact_mod_cast hC n
    simpa only [Nat.cast_mul,Nat.cast_pow,mul_comm] using hc
  · simpa only [mul_comm (C:ℝ)] using tendsto_normalized_polynomial p zs.length (dimension R)
      (Nat.Prime.one_lt Fact.out) hd C
end Lech

end

end OAI
