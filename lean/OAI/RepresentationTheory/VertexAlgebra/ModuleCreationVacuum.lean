import OAI.RepresentationTheory.VertexAlgebra.ModuleCreationModel

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

def creationVacuumCoefficient (a : W) (n : ℕ) : Completion W :=
  ((n.factorial:ℂ)⁻¹) • (((M.virasoroMode (-1)^n) a : W) : Completion W)

@[simp] theorem creationVacuumCoefficient_zero (a : W) :
    M.creationVacuumCoefficient a 0 = (a : Completion W) := by
  simp [creationVacuumCoefficient]

theorem creationVacuumCoefficient_eq_creationMode (a : W) (n : ℕ) :
    M.creationVacuumCoefficient a n = (M.creationMode a (-(n:ℤ)-1) A.vacuum : Completion W) := by
  rw [M.creationMode_vacuum, Completion.coe_smul]
  rfl

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

theorem creationVacuumCoefficient_norm (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) (n : ℕ) :
    ‖M.creationVacuumCoefficient x n‖ ≤ (1+(n:ℝ))^(h+1)*‖x‖ := by
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : (h+2).ascFactorial n ≤ n.factorial * (n+1)^(h+1) := by
    rw [show h+2 = (h+1)+1 by omega, Nat.ascFactorial_eq_factorial_mul_choose]
    apply Nat.mul_le_mul_left
    have H := Nat.choose_add_le_add_one_pow n (h+1)
    rw [Nat.add_comm n (h+1), Nat.choose_symm_add] at H
    exact H
  have hc' : ((h+2).ascFactorial n:ℝ) ≤ (n.factorial:ℝ)*(1+(n:ℝ))^(h+1) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, add_comm (n:ℝ)]
      using (show ((h+2).ascFactorial n:ℝ) ≤ (n.factorial * (n+1)^(h+1):ℕ) by exact_mod_cast hc)
  calc
    ‖M.creationVacuumCoefficient x n‖ = (n.factorial:ℝ)⁻¹ * ‖(M.virasoroMode (-1)^n) x‖ := by
      simp [creationVacuumCoefficient, norm_smul]
    _ ≤ (n.factorial:ℝ)⁻¹ * (((h+2).ascFactorial n:ℝ)*‖x‖) := by
      gcongr
      exact Q.translation_pow_norm t hx n
    _ ≤ (n.factorial:ℝ)⁻¹ * ((n.factorial:ℝ)*(1+(n:ℝ))^(h+1)*‖x‖) := by gcongr
    _ = _ := by field_simp

theorem creationVacuumSeries_summable (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z^n • M.creationVacuumCoefficient x n‖) := by
  have hs := (LocalSkewFlow.summable_shifted_pow_geometric 1 zero_le_one (h+1)
    (norm_nonneg z) hz).mul_right ‖x‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro n
  rw [norm_smul, norm_pow]
  calc
    _ ≤ ‖z‖^n*((1+(n:ℝ))^(h+1)*‖x‖) := by
      gcongr
      exact Q.creationVacuumCoefficient_norm t hx n
    _ = _ := by ring

theorem creationVacuumSmear_summable (t : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade t h) (f : SmoothCircleFunction) :
    Summable (fun n : ℕ => ‖f.coefficient (-(n:ℤ)) • M.creationVacuumCoefficient x n‖) := by
  have hs := (summable_int_iff_summable_nat_and_neg.mp (f.rapid_coefficients (h+1))).2
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] at hs
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_right ‖x‖)
  intro n
  rw [norm_smul, mul_assoc]
  gcongr
  exact Q.creationVacuumCoefficient_norm t hx n

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
