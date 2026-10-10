import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpPolynomial

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
theorem polynomial_power_contraction_bounded (X : EnergyBand → ℕ → ℝ) (hX : ∀ τ N, 1 ≤ X τ N)
    (hm : ∀ τ, Monotone (X τ)) (hp : PolynomialCutoffControl X)
    (K P : ℕ) (hK : 1 ≤ K) (hP : 1 ≤ P) (C : ℝ) (hC : 1 ≤ C)
    (H : ∀ τ N, X τ N^P ≤ C*X τ (K*N)^(P-1)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ τ N, X τ N ≤ B := by
  obtain ⟨D, hD, p, HD⟩ := hp
  let A := (D+1)*2^p
  have hA : 0 < A := by dsimp [A]; positivity
  have hPR : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPR1 : 1 ≤ (P : ℝ) := by exact_mod_cast hP
  let ρ : ℝ := 1-(P : ℝ)⁻¹
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; linarith [(inv_le_one₀ hPR).mpr hPR1]
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [inv_pos.mpr hPR]
  let c := Real.log C/(P : ℝ)
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg hC) hPR.le
  have hstart (τ : EnergyBand) (N : ℕ) (hN : 1 ≤ N) : Real.log (X τ N) ≤ Real.log A + (p : ℝ)*Real.log N := by
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNR : (0 : ℝ) < N := by linarith
    have HX : X τ N ≤ A*(N : ℝ)^p := by
      apply (HD τ N).trans
      calc
        _ ≤ (D+1)*(2*(N : ℝ))^p := by gcongr <;> linarith
        _ = _ := by dsimp [A]; rw [mul_pow]; ring
    have HH := Real.log_le_log (by linarith [hX τ N] : 0 < X τ N) HX
    rwa [Real.log_mul hA.ne' (pow_pos hNR p).ne', Real.log_pow] at HH
  have hstep (τ : EnergyBand) (N : ℕ) (_hN : 1 ≤ N) : Real.log (X τ N) ≤ c+ρ*Real.log (X τ (K*N)) := by
    have hx : 0 < X τ N := by linarith [hX τ N]
    have hy : 0 < X τ (K*N) := by linarith [hX τ (K*N)]
    have HL := Real.log_le_log (pow_pos hx P) (H τ N)
    rw [Real.log_mul (by linarith : C ≠ 0) (pow_ne_zero _ hy.ne'), Real.log_pow,
      Real.log_pow, Nat.cast_sub hP, Nat.cast_one] at HL
    have he : c+ρ*Real.log (X τ (K*N)) =
        (Real.log C+((P : ℝ)-1)*Real.log (X τ (K*N)))/(P : ℝ) := by
      dsimp [c, ρ]
      field_simp
    rw [he]
    exact (le_div_iff₀ hPR).mpr (by simpa only [mul_comm] using HL)
  have HB (τ : EnergyBand) := multiplicative_cutoff_log_bound (fun N => Real.log (X τ N)) K hK
    ρ c (Real.log A) p hρ0 hρ1 hc (hstart τ) (hstep τ)
  let B := Real.exp (c/(1-ρ))
  have HB1 : 1 ≤ B := Real.one_le_exp_iff.mpr (div_nonneg hc (by linarith))
  have HBN (τ : EnergyBand) (N : ℕ) (hN : 1 ≤ N) : X τ N ≤ B := by
    have hx : 0 < X τ N := by linarith [hX τ N]
    simpa [B, Real.exp_log hx] using Real.exp_le_exp.mpr (HB τ N hN)
  exact ⟨B, HB1, fun τ N => if hN : 1 ≤ N then HBN τ N hN else
    (hm τ (show N ≤ 1 by omega)).trans (HBN τ 1 le_rfl)⟩

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem exists_bounded_sharpGrowth (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ X : EnergyBand → ℕ → ℝ, (∀ τ N, 1 ≤ X τ N) ∧ (∀ τ, Monotone (X τ)) ∧
      (∃ B : ℝ, 1 ≤ B ∧ ∀ τ N, X τ N ≤ B) ∧
      (∀ e, ∀ b ∈ A.grade e, M.SharpGrowth X b e) := by
  obtain ⟨D, hD, S, _hSzero, hS, _hspan, _hcut, H⟩ := Q.exists_sharpMajorant hc
  have hp := Q.polynomialEnergyBounds hc
  obtain ⟨C, hC, HC⟩ := Q.sharpMajorant_power_contraction D hD S hS hp H
  have HB := polynomial_power_contraction_bounded (fun τ => M.sharpMajorant τ D S)
    (fun τ => M.one_le_sharpMajorant τ D S) (fun τ => M.sharpMajorant_mono τ D S)
    (Q.sharpMajorant_polynomial D S (fun d a ha => (hS d a ha).1) hp)
    2 (2*D) (by decide) (by omega) C hC HC
  exact ⟨(fun τ => M.sharpMajorant τ D S), (fun τ => M.one_le_sharpMajorant τ D S), (fun τ => M.sharpMajorant_mono τ D S), HB, H⟩

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
