import Mathlib
import OAI.RingTheory.Multiplicity.IdealGradedLengthPiece
import OAI.RingTheory.Multiplicity.MinimalReduction

namespace OAI

noncomputable section
open IsLocalRing Filter
open scoped Topology
namespace Lech.MinimalReduction
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma shifted_colength_limit (c : ℕ) :
    Tendsto (fun n : ℕ => (Nat.factorial (dimension R):ℝ) *
      (colength R (n+c):ℝ) / (n:ℝ)^dimension R) atTop (𝓝 (multiplicity R)) := by
  have hn : Tendsto (fun n : ℕ => ((n+c:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1:ℝ)) := by
    simpa only [inv_div,inv_one,Nat.cast_add] using
      (tendsto_natCast_div_add_atTop (c:ℝ)).inv₀ (by norm_num)
  have H := ((multiplicity_is_limit R).comp (tendsto_add_atTop_nat c)).mul
    (hn.pow (dimension R))
  simp only [one_pow,mul_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hnc : ((n+c:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : n+c≠0)
  dsimp [normalizedColength]
  rw [div_pow]
  field_simp

lemma reduction_multiplicity {J : Ideal R} {c : ℕ} (hJ : J ≤ maximalIdeal R)
    (h : (maximalIdeal R)^(c+1)=J*(maximalIdeal R)^c) :
    Primary.multiplicity J = multiplicity R := by
  have hprim : J.radical=maximalIdeal R := reduction_primary hJ h
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto (Primary.multiplicity_is_limit J hprim)
      (shifted_colength_limit c)
    exact Eventually.of_forall fun n => by
      have hc : Primary.colength J n ≤ colength R (n+c) := by
        have H := length_quotient_le R (reduction_power_le h n)
        rw [← Primary.colength_cast J hprim n,← colength_cast R (n+c)] at H
        exact ENat.natCast_le_natCast.mp H
      dsimp [Primary.normalizedColength]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)) (by positivity)
  · have hh : (maximalIdeal R).radical=maximalIdeal R := Ideal.IsPrime.radical inferInstance
    exact Primary.multiplicity_antitone hprim hh hJ

 

theorem exists_minimal_reduction [Infinite (ResidueField R)] :
    ∃ z : Fin (dimension R) → R, (∀ i,z i ∈ maximalIdeal R) ∧
      (Ideal.span (Set.range z)).radical=maximalIdeal R ∧
      Primary.multiplicity (Ideal.span (Set.range z))=multiplicity R ∧
      ∃ c : ℕ,∀ n,(maximalIdeal R)^(n+c) ≤ (Ideal.span (Set.range z))^n := by
  obtain ⟨z,hz,c,hc⟩ := exists_reduction (R:=R)
  have hJ : Ideal.span (Set.range z) ≤ maximalIdeal R :=
    Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hz i)
  exact ⟨z,hz,reduction_primary hJ hc,reduction_multiplicity hJ hc,c,
    reduction_power_le hc⟩
end Lech.MinimalReduction

end

end OAI
