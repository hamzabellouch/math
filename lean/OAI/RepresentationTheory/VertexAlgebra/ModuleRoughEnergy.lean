import OAI.RepresentationTheory.VertexAlgebra.ModuleBootstrap
import OAI.RepresentationTheory.VertexAlgebra.ModuleSpectralNorms

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Q : M.UnitaryStructure U)
include Q

theorem energyBound_of_polynomial_blocks {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t N,
      M.BlockControl t a d N (C * (1 + (N : ℝ))^p)) : M.PolynomialEnergyBound a := by
  obtain ⟨C, hC, p, hp⟩ := H
  let K : ℝ := (C + 1) * ((d : ℝ) + 2)^p
  have hK : 0 < K := by dsimp [K]; positivity
  have hband (t : EnergyBand) (n : ℤ) (h : ℕ) (b : W) (hb : b ∈ M.bandGrade t h) :
      ‖mode M.fields a n b‖ ≤ K * (1 + |(n : ℝ)|)^p * (1 + (h : ℝ))^p * ‖b‖ := by
    by_cases hout : 0 ≤ (h : ℤ) + d - n - 1
    · let k := ((h : ℤ) + d - n - 1).toNat
      let N := h + d + 1 + n.natAbs
      have hk : (k : ℤ) = (h : ℤ) + d - n - 1 := Int.toNat_of_nonneg hout
      have hnabs : -n ≤ (n.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
      have hhN : h ≤ N := by dsimp [N]; omega
      have hkN : k ≤ N := by dsimp [N]; omega
      have hindex : (h : ℤ) - k + d - 1 = n := by omega
      have hblock := hp t N h hhN k hkN b hb
      simp only [physicalMode, hindex] at hblock
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      have hN : 1 + (N : ℝ) ≤ ((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)) := by
        dsimp [N]
        push_cast
        rw [habs]
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
        have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
        nlinarith [mul_nonneg hd0 hn0, mul_nonneg hd0 hh0, mul_nonneg hn0 hh0,
          mul_nonneg (mul_nonneg hd0 hn0) hh0]
      apply hblock.trans
      have hc : C ≤ C + 1 := by linarith
      calc
        _ ≤ ((C + 1) * (((d : ℝ) + 2) * (1 + |(n : ℝ)|) * (1 + (h : ℝ)))^p) * ‖b‖ := by
          gcongr
        _ = _ := by dsimp [K]; simp only [mul_pow]; ring
    · have hz : mode M.fields a n b=0 := by
        have hz := Q.physicalMode_eq_zero_above_band t ha hb (n-d+1) (by omega)
        simpa only [physicalMode, show n-(d:ℤ)+1+d-1=n by omega] using hz
      rw [hz, norm_zero]
      positivity
  have hgrade (n : ℤ) (z : ℂ) (b : W) (hb : b ∈ M.grade z) :
      ‖mode M.fields a n b‖ ≤ K * (1+|(n:ℝ)|)^p * (1+z.re)^p * ‖b‖ := by
    by_cases h0 : b=0
    · simp [h0]
    obtain ⟨t,h,hz⟩ := Q.exists_band_of_mem hb h0
    subst z
    have H := hband t n h b hb
    apply H.trans
    have ht := t.property.1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    gcongr
    linarith
  refine ⟨K, hK, p, p, ?_⟩
  intro n b
  simp only [Int.cast_abs]
  let L := K * (1 + |(n : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖mode M.fields a n b‖^2 ≤ (L * ‖(M.energyShift^p) b‖)^2
  rw [Q.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ M.gradeSupport b, (L * (1 + h.re)^p * ‖M.gradeComponent h b‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      have hg := hgrade n h _ (M.gradeComponent_mem h b)
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hg)).mpr hg
    _ = L^2 * ∑ h ∈ M.gradeSupport b, ((1 + h.re)^p * ‖M.gradeComponent h b‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← Q.energy_norm_sq_eq_sum_grades]; ring

theorem energyBound_add {a b : V} (ha : M.PolynomialEnergyBound a)
    (hb : M.PolynomialEnergyBound b) : M.PolynomialEnergyBound (a + b) := by
  obtain ⟨C, hC, p, k, hp⟩ := ha
  obtain ⟨D, hD, q, l, hq⟩ := hb
  refine ⟨C + D, add_pos hC hD, p + q, k + l, ?_⟩
  intro n c
  simp only [Int.cast_abs] at hp hq ⊢
  have hbase : 1 ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
  have hpp : (1 + |(n : ℝ)|)^p ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hqq : (1 + |(n : ℝ)|)^q ≤ (1 + |(n : ℝ)|)^(p + q) :=
    pow_le_pow_right₀ hbase (by omega)
  have hkk := Q.energyShift_pow_norm_mono (show k ≤ k + l by omega) c
  have hll := Q.energyShift_pow_norm_mono (show l ≤ k + l by omega) c
  rw [mode_add, LinearMap.add_apply]
  calc
    _ ≤ ‖mode M.fields a n c‖ + ‖mode M.fields b n c‖ := norm_add_le _ _
    _ ≤ C * (1 + |(n : ℝ)|)^p * ‖(M.energyShift^k) c‖ +
          D * (1 + |(n : ℝ)|)^q * ‖(M.energyShift^l) c‖ := add_le_add (hp n c) (hq n c)
    _ ≤ C * (1 + |(n : ℝ)|)^(p + q) * ‖(M.energyShift^(k + l)) c‖ +
          D * (1 + |(n : ℝ)|)^(p + q) * ‖(M.energyShift^(k + l)) c‖ := by gcongr
    _ = _ := by ring

 

theorem polynomialEnergyBounds (hc : A.toVertexAlgebra.C2Cofinite) : M.PolynomialEnergyBounds := by
  obtain ⟨D, hD, S, _, hS, H⟩ := Q.exists_generatorMajorant hc
  obtain ⟨C, hC, p, hp⟩ := Q.generatorMajorant_polynomial D hD S hS H
  have hB := M.one_le_generatorMajorant D S
  have hhom (d : ℕ) (a : V) (ha : a ∈ A.grade d) : M.PolynomialEnergyBound a := by
    obtain ⟨K, hK, q, hq⟩ := H d a ha
    apply Q.energyBound_of_polynomial_blocks ha
    refine ⟨K * C^d, by positivity, q + p * d, ?_⟩
    intro t N
    apply M.blockControl_mono (hq t N)
    have hBN : 0 ≤ M.generatorMajorant D S t N := zero_le_one.trans (hB t N)
    calc
      _ ≤ K * (1 + (N : ℝ))^q * (C * (1 + (N : ℝ))^p)^d := by gcongr; exact hp t N
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  intro a
  exact A.homogeneous_induction (P := M.PolynomialEnergyBound)
    (hhom 0 0 (Submodule.zero_mem _)) hhom (fun _ _ => Q.energyBound_add) a

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
