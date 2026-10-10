import OAI.RepresentationTheory.VertexAlgebra.ModuleCutoffs
import OAI.RepresentationTheory.VertexAlgebra.ModuleSl2Bound

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

def mobiusGenerator : Module.End ℂ W :=
  (2 : ℂ)⁻¹ • (M.virasoroMode 1 - M.virasoroMode (-1))

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

theorem virasoro_neg_one_norm_on_band (τ : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.bandGrade τ h) :
    ‖M.virasoroMode (-1) x‖ ≤ 4*(1+(h:ℝ))*‖x‖ := by
  have hp := Q.virasoro_one_norm_on_band τ hx
  have hs := Q.sl2_norm_difference hx
  simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re] at hs
  have hp' := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have ht := τ.property.2
  have h0 : (0:ℝ) ≤ h := Nat.cast_nonneg h
  have hh : 2*(τ.val+(h:ℝ)) ≤ 12*(1+(h:ℝ))^2 := by nlinarith
  have ht' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [hp', ht']

theorem mode_norm_on_cutoff_of_band (τ : EnergyBand) {a : V} {d N : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ h ≤ N, ∀ x ∈ M.bandGrade τ h, ‖mode M.fields a n x‖ ≤ C*‖x‖)
    {x : W} (hx : x ∈ M.energyCutoff τ N) : ‖mode M.fields a n x‖ ≤ C*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [Q.mode_norm_sq_eq_sum_cutoff τ ha n hx, mul_pow,
    Q.norm_sq_eq_sum_cutoff τ hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have Hb := H h (by have := Finset.mem_range.mp hh; omega) _ (M.bandComponent_mem τ h x)
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) Hb 2

theorem virasoro_one_norm_cutoff (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) :
    ‖M.virasoroMode 1 x‖ ≤ 2*(1+(N:ℝ))*‖x‖ := by
  apply Q.mode_norm_on_cutoff_of_band τ A.conformal_mem 2 (by positivity) _ hx
  intro h hh y hy
  apply (Q.virasoro_one_norm_on_band τ hy).trans
  gcongr

theorem virasoro_neg_one_norm_cutoff (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) :
    ‖M.virasoroMode (-1) x‖ ≤ 4*(1+(N:ℝ))*‖x‖ := by
  apply Q.mode_norm_on_cutoff_of_band τ A.conformal_mem 0 (by positivity) _ hx
  intro h hh y hy
  apply (Q.virasoro_neg_one_norm_on_band τ hy).trans
  gcongr

theorem mobiusGenerator_mem_energyCutoff (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) : M.mobiusGenerator x ∈ M.energyCutoff τ (N+1) := by
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact Q.physicalMode_mem_cutoff τ A.conformal_mem hx 1 (K := N+1) (by omega)
  · exact Q.physicalMode_mem_cutoff τ A.conformal_mem hx (-1) (K := N+1) (by omega)

theorem mobiusGenerator_pow_mem_energyCutoff (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) (n : ℕ) :
    (M.mobiusGenerator^n) x ∈ M.energyCutoff τ (N+n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using
      Q.mobiusGenerator_mem_energyCutoff τ ih

theorem mobiusGenerator_skew (x y : W) :
    inner ℂ (M.mobiusGenerator x) y = -inner ℂ x (M.mobiusGenerator y) := by
  simp only [mobiusGenerator, LinearMap.smul_apply, LinearMap.sub_apply,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    Q.virasoro_adjoint, neg_neg, map_inv₀, map_ofNat]
  ring

theorem mobiusGenerator_norm_cutoff (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) : ‖M.mobiusGenerator x‖ ≤ 8*(1+(N:ℝ))*‖x‖ := by
  have hp := Q.virasoro_one_norm_cutoff τ hx
  have hn := Q.virasoro_neg_one_norm_cutoff τ hx
  calc
    _ = (1/2:ℝ)*‖M.virasoroMode 1 x-M.virasoroMode (-1) x‖ := by
      simp [mobiusGenerator, norm_smul]
    _ ≤ (1/2:ℝ)*(‖M.virasoroMode 1 x‖+‖M.virasoroMode (-1) x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ _ := by nlinarith [norm_nonneg x, Nat.cast_nonneg (α:=ℝ) N]

theorem mobiusGenerator_pow_norm (τ : EnergyBand) {N : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ N) (n : ℕ) :
    ‖(M.mobiusGenerator^n) x‖ ≤ (8:ℝ)^n*((N+1).ascFactorial n:ℝ)*‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc
      _ ≤ 8*(1+((N+n:ℕ):ℝ))*‖(M.mobiusGenerator^n) x‖ :=
        Q.mobiusGenerator_norm_cutoff τ (Q.mobiusGenerator_pow_mem_energyCutoff τ hx n)
      _ ≤ 8*(1+((N+n:ℕ):ℝ))*((8:ℝ)^n*((N+1).ascFactorial n:ℝ)*‖x‖) := by gcongr
      _ = _ := by rw [Nat.ascFactorial_succ, pow_succ]; push_cast; ring

theorem mobiusTaylor_mem_energyCutoff (τ : EnergyBand) {h : ℕ} {x : W}
    (hx : x ∈ M.energyCutoff τ h) (t : ℝ) (N : ℕ) :
    LocalSkewFlow.skewTaylor M.mobiusGenerator t N x ∈ M.energyCutoff τ (h+N) := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact M.energyCutoff_mono τ (by have := Finset.mem_range.mp hn; omega)
    (Q.mobiusGenerator_pow_mem_energyCutoff τ hx n)

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
