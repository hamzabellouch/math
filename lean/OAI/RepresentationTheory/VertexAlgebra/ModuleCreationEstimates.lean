import OAI.RepresentationTheory.VertexAlgebra.ModuleMobiusEstimates

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Q : M.UnitaryStructure U)
include Q

theorem virasoro_one_norm_sq_sharp_band (t : EnergyBand) :
    ∀ (h : ℕ) (x : W), x ∈ M.bandGrade t h →
      ‖M.virasoroMode 1 x‖^2 ≤ (h:ℝ)*(h+1)*‖x‖^2 := by
  intro h
  induction h with
  | zero =>
    intro x hx
    have hz := Q.physicalMode_eq_zero_above_band t A.conformal_mem hx (1:ℤ)
      (by omega : (0:ℤ) < 1)
    rw [M.physicalMode_conformal] at hz
    simp [hz]
  | succ h ih =>
    intro x hx
    have hb := M.virasoro_mem_band t hx 1 (k := h) (by omega)
    have hi := ih (M.virasoroMode 1 x) hb
    have hd := Q.sl2_norm_difference hb
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re] at hd
    have her : ‖M.virasoroMode (-1) (M.virasoroMode 1 x)‖^2 ≤
        ((h:ℝ)+1)*(h+2)*‖M.virasoroMode 1 x‖^2 := by
      have ht' := mul_le_mul_of_nonneg_right (le_of_lt t.property.2)
        (sq_nonneg ‖M.virasoroMode 1 x‖)
      nlinarith
    have hh : U.IsHermitian 2 A.conformalVector := by
      simp [CFTTypeVOA.UnitaryStructure.IsHermitian, U.pct_conformal]
    have hcs := Q.mode_norm_sq_le_adjoint A.conformal_mem A.conformal_quasiPrimary hh 1 x
    simp only [M.physicalMode_conformal] at hcs
    by_cases hz : ‖M.virasoroMode 1 x‖ = 0
    · rw [hz, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · have hp := sq_pos_of_ne_zero hz
      apply (mul_le_mul_iff_of_pos_right hp).mp
      calc
        _ ≤ (‖x‖*‖M.virasoroMode (-1) (M.virasoroMode 1 x)‖)^2 := by
          nlinarith [sq_nonneg (‖x‖*‖M.virasoroMode (-1) (M.virasoroMode 1 x)‖ -
            ‖M.virasoroMode 1 x‖^2)]
        _ = ‖x‖^2 * ‖M.virasoroMode (-1) (M.virasoroMode 1 x)‖^2 := mul_pow _ _ _
        _ ≤ ‖x‖^2 * (((h:ℝ)+1)*(h+2)*‖M.virasoroMode 1 x‖^2) :=
          mul_le_mul_of_nonneg_left her (sq_nonneg _)
        _ = _ := by push_cast; ring

theorem virasoro_neg_one_norm_sharp_band (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) : ‖M.virasoroMode (-1) x‖ ≤ ((h:ℝ)+2)*‖x‖ := by
  have hi := Q.virasoro_one_norm_sq_sharp_band t h x hx
  have hd := Q.sl2_norm_difference hx
  simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re] at hd
  have ht := mul_le_mul_of_nonneg_right (le_of_lt t.property.2) (sq_nonneg ‖x‖)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h0 : 0 ≤ (h:ℝ)*‖x‖^2 := mul_nonneg (Nat.cast_nonneg h) (sq_nonneg _)
  nlinarith [sq_nonneg ‖x‖]

omit Q in
theorem translation_pow_mem_band (_unitaryStructure : M.UnitaryStructure U)
    (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) (n : ℕ) :
    (M.virasoroMode (-1)^n) x ∈ M.bandGrade t (h+n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact M.virasoro_mem_band t ih (-1) (by omega)

theorem translation_pow_norm (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) (n : ℕ) :
    ‖(M.virasoroMode (-1)^n) x‖ ≤ ((h+2).ascFactorial n:ℝ)*‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc
      _ ≤ (((h+n:ℕ):ℝ)+2)*‖(M.virasoroMode (-1)^n) x‖ :=
        Q.virasoro_neg_one_norm_sharp_band t (Q.translation_pow_mem_band t hx n)
      _ ≤ (((h+n:ℕ):ℝ)+2)*(((h+2).ascFactorial n:ℝ)*‖x‖) := by gcongr
      _ = _ := by rw [Nat.ascFactorial_succ]; push_cast; ring

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
