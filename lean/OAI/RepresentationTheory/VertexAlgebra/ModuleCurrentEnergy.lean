import OAI.RepresentationTheory.VertexAlgebra.ModuleOptimalEnergy

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem current_linear_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 1 a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖M.physicalMode a 1 m v‖ ≤
      C*(1+|(m : ℝ)|)*‖M.energyShift v‖ := by
  obtain ⟨X, hX, _hm, ⟨B, hB, HB⟩, H⟩ := Q.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := (H 1 a ha).1
  have HR (τ : EnergyBand) (N : ℕ) : M.positiveColumnNorm τ a 1 N ≤ (C+1)*B*(N+1 : ℝ) := by
    have Hsq := positiveColumnNorm_sq_le τ (by positivity : 0 ≤ C*(N+1 : ℝ)*X τ N^2)
      (by simpa only [ColumnControl, show 2*1-1=1 by decide, show 2*1=2 by decide, pow_one] using HC τ N)
    have hXN := zero_le_one.trans (hX τ N)
    have hCX : C*(N+1 : ℝ)*X τ N^2 ≤ C*(N+1 : ℝ)*B^2 := by gcongr; exact HB τ N
    apply (sq_le_sq₀ (M.positiveColumnNorm_nonneg τ a 1 N) (by positivity)).mp
    apply Hsq.trans (hCX.trans _)
    have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hcc : C ≤ (C+1)^2 := by nlinarith
    calc
      _ ≤ (C+1)^2*(N+1 : ℝ)^2*B^2 := by gcongr; nlinarith
      _ = _ := by ring
  let K := (C+1)*B
  have hK : 0 < K := by dsimp [K]; positivity
  have Hcut (τ : EnergyBand) (N : ℕ) (m : ℤ) v (hv : v ∈ M.energyCutoff τ N) :
      ‖M.physicalMode a 1 m v‖ ≤ K*(1+|(m : ℝ)|)^1*(N+1 : ℝ)^1*‖v‖ := by
    have HR' (n : ℕ) : M.positiveColumnNorm τ a 1 n ≤ K*(n+1 : ℝ) := HR τ n
    rcases m with m | m
    · apply (Q.positive_mode_norm_le_column τ ha hv m).trans
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), pow_one]
      calc
        _ ≤ K*(N+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' N) (norm_nonneg _)
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v),
          mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v))]
    · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
      rw [he]
      apply (Q.negative_mode_norm_le_column τ ha hq hh hv (m+1)).trans
      simp only [Int.cast_neg, abs_neg, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)), pow_one]
      calc
        _ ≤ K*((N+(m+1) : ℕ)+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' (N+(m+1))) (norm_nonneg _)
        _ ≤ _ := by
          have hbase : (((N+(m+1) : ℕ) : ℝ)+1) ≤ (1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ) := by
            push_cast
            have hh := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) N)
            nlinarith [Nat.cast_nonneg (α := ℝ) N]
          calc
            _ ≤ K*((1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ))*‖v‖ := by gcongr
            _ = _ := by ring
  refine ⟨K, hK, ?_⟩
  simpa only [pow_one] using Q.physical_energyBound_of_cutoffs ha hK.le Hcut

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
