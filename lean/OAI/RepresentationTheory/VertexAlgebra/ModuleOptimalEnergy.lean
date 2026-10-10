import OAI.RepresentationTheory.VertexAlgebra.ModuleOptimalCutoff

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Q : M.UnitaryStructure U)
include Q

 

theorem physical_energyBound_of_cutoffs {a : V} {d p k : ℕ} {C : ℝ}
    (ha : a ∈ A.grade d) (hC : 0 ≤ C)
    (H : ∀ τ N (m : ℤ) v, v ∈ M.energyCutoff τ N →
      ‖M.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*(N+1 : ℝ)^k*‖v‖) :
    ∀ (m : ℤ) v, ‖M.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^p*‖(M.energyShift^k) v‖ := by
  classical
  intro m v
  let L := C*(1+|(m : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hgrade (z : ℂ) (b : W) (hb : b ∈ M.grade z) :
      ‖M.physicalMode a d m b‖ ≤ L*(1+z.re)^k*‖b‖ := by
    by_cases h0 : b = 0
    · simp [h0]
    obtain ⟨τ,h,hz⟩ := Q.exists_band_of_mem hb h0
    subst z
    have HH := H τ h m b (M.grade_le_energyCutoff τ le_rfl hb)
    apply HH.trans
    have ht := τ.property.1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
    dsimp [L]
    have he : (h : ℝ)+1 ≤ 1+((τ : ℝ)+(h : ℝ)) := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he k) hL)
      (norm_nonneg b)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖M.physicalMode a d m v‖^2 ≤ (L*‖(M.energyShift^k) v‖)^2
  rw [physicalMode, Q.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ M.gradeSupport v, (L*(1+h.re)^k*‖M.gradeComponent h v‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      have hg := hgrade h _ (M.gradeComponent_mem h v)
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hg)).mpr hg
    _ = L^2 * ∑ h ∈ M.gradeSupport v, ((1+h.re)^k*‖M.gradeComponent h v‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← Q.energy_norm_sq_eq_sum_grades]; ring

 

theorem optimal_quasiPrimary_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖M.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^(2*d)*‖(M.energyShift^(d-1)) v‖ := by
  obtain ⟨C, hC, H⟩ := Q.optimal_quasiPrimary_cutoff hc ha hq hh hd
  exact ⟨C, hC, Q.physical_energyBound_of_cutoffs ha hC.le H⟩

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
