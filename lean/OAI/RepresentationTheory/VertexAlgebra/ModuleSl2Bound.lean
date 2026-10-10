import OAI.RepresentationTheory.VertexAlgebra.ModuleAdjointDescent

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Q : M.UnitaryStructure U)
include Q

 

theorem virasoro_one_norm_on_band (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) :
    ‖M.virasoroMode 1 x‖ ≤ 2*(1+(h:ℝ))*‖x‖ := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [CFTTypeVOA.UnitaryStructure.IsHermitian, U.pct_conformal]
  have H (e : ℕ) (he : e ≤ h) (y : W) (hy : y ∈ M.bandGrade t e) :
      ‖M.selfCommutator A.conformalVector 2 (1:ℕ) y‖ ≤ 2*(1+(h:ℝ))*‖y‖ := by
    rw [selfCommutator_apply]
    simp only [M.physicalMode_conformal, Nat.cast_one]
    rw [M.sl2_commutator, M.virasoro_zero_on_grade hy, smul_smul, norm_smul]
    have hc : (2:ℂ)*((t.val:ℂ)+e) = ((2*(t.val+(e:ℝ)):ℝ):ℂ) := by push_cast; rfl
    have ht := t.property.1
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    have her : (e:ℝ) ≤ h := by exact_mod_cast he
    linarith [t.property.2]
  have hb := Q.lowering_norm_sq_of_commutator t A.conformal_mem A.conformal_quasiPrimary hh
    (by decide : 0 < 1) (by positivity : 0 ≤ 2*(1+(h:ℝ))) H h le_rfl x hx
  simp only [Nat.cast_one, M.physicalMode_conformal] at hb
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (h:ℝ)*(2*(1+(h:ℝ)))*‖x‖^2 := hb
    _ ≤ (2*(1+(h:ℝ))*‖x‖)^2 := by
      have h0 : (0:ℝ) ≤ h := Nat.cast_nonneg h
      nlinarith [sq_nonneg ‖x‖, mul_nonneg h0 (sq_nonneg ‖x‖)]
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
