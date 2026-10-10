import OAI.RepresentationTheory.VertexAlgebra.ModuleCutoffs
import OAI.RepresentationTheory.VertexAlgebra.ModuleAdjointDescent

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
variable (τ : EnergyBand)
def positiveColumn (a : V) (d N : ℕ) :
    M.energyCutoff τ N →L[ℂ] PiLp 2 (fun _ : Fin (N + 1) => W) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (Fin (N + 1) → W)).symm.toLinearMap.comp
      (LinearMap.pi (fun m => (M.physicalMode a d m).comp (M.energyCutoff τ N).subtype)))

@[simp]
theorem positiveColumn_apply (a : V) (d N : ℕ) (v : M.energyCutoff τ N)
    (m : Fin (N + 1)) : (M.positiveColumn τ a d N v).ofLp m = M.physicalMode a d m v := rfl

 
def positiveColumnNorm (a : V) (d N : ℕ) : ℝ := ‖M.positiveColumn τ a d N‖

theorem positiveColumnNorm_nonneg (a : V) (d N : ℕ) :
    0 ≤ M.positiveColumnNorm τ a d N := norm_nonneg (M.positiveColumn τ a d N)

theorem positiveColumn_norm_sq (a : V) (d N : ℕ) (v : M.energyCutoff τ N) :
    ‖M.positiveColumn τ a d N v‖^2 =
      ∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [positiveColumn_apply]
  exact Fin.sum_univ_eq_sum_range (fun m => ‖M.physicalMode a d m v‖^2) (N + 1)

theorem sum_positive_modes_sq_le (a : V) (d : ℕ) {N : ℕ} {v : W}
    (hv : v ∈ M.energyCutoff τ N) :
    (∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2) ≤
      M.positiveColumnNorm τ a d N ^ 2 * ‖v‖^2 := by
  rw [← M.positiveColumn_norm_sq τ a d N ⟨v, hv⟩, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((M.positiveColumn τ a d N).le_opNorm ⟨v, hv⟩) 2

theorem positiveColumnNorm_mono (a : V) (d : ℕ) :
    Monotone (M.positiveColumnNorm τ a d) := by
  intro N K hNM
  apply ContinuousLinearMap.opNorm_le_bound _ (M.positiveColumnNorm_nonneg τ a d K)
  intro v
  have hR := M.positiveColumnNorm_nonneg τ a d K
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, M.positiveColumn_norm_sq τ]
  calc
    _ ≤ ∑ m ∈ Finset.range (K + 1), ‖M.physicalMode a d m v‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      positivity
    _ ≤ _ := M.sum_positive_modes_sq_le τ a d (M.energyCutoff_mono τ hNM v.property)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem positive_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : W} (hv : v ∈ M.energyCutoff τ N) (m : ℕ) :
    ‖M.physicalMode a d m v‖ ≤ M.positiveColumnNorm τ a d N * ‖v‖ := by
  have hR := M.positiveColumnNorm_nonneg τ a d N
  by_cases hm : N < m
  · rw [Q.physicalMode_zero_above_cutoff τ ha hv m (by exact_mod_cast hm), norm_zero]
    positivity
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow]
    apply le_trans _ (M.sum_positive_modes_sq_le τ a d hv)
    exact Finset.single_le_sum (f := fun i : ℕ => ‖M.physicalMode a d i v‖^2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (show m < N + 1 by omega))

theorem finsum_positive_modes_sq_eq {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : W} (hv : v ∈ M.energyCutoff τ N) :
    (∑ᶠ m : ℕ, ‖M.physicalMode a d m v‖^2) =
      ∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2 := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro m hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hm
  change ‖M.physicalMode a d m v‖^2 = 0
  rw [Q.physicalMode_zero_above_cutoff τ ha hv m (by omega)]
  simp

theorem negative_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {v : W} (hv : v ∈ M.energyCutoff τ N) (m : ℕ) :
    ‖M.physicalMode a d (-(m : ℤ)) v‖ ≤ M.positiveColumnNorm τ a d (N + m) * ‖v‖ := by
  have hR := M.positiveColumnNorm_nonneg τ a d (N + m)
  have hmem := Q.physicalMode_mem_cutoff τ ha hv (-(m : ℤ)) (K := N + m) (by omega)
  have hb := Q.positive_mode_norm_le_column τ ha hmem m
  have hs := Q.mode_norm_sq_le_adjoint ha hq hh (-(m : ℤ)) v
  simp only [neg_neg] at hs
  have h := hs.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg v))
  by_cases hx : ‖M.physicalMode a d (-(m : ℤ)) v‖ = 0
  · rw [hx]; positivity
  · have hxpos : 0 < ‖M.physicalMode a d (-(m : ℤ)) v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply (mul_le_mul_iff_of_pos_right hxpos).mp
    nlinarith [h]

 

theorem shifted_column_sq_le {a : V} {d N s J : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {v : W} (hv : v ∈ M.energyCutoff τ N) :
    (∑ j ∈ Finset.range J, ‖M.physicalMode a d ((j : ℤ) - s) v‖^2) ≤
      ((s : ℝ) + 1) * M.positiveColumnNorm τ a d (N + s)^2 * ‖v‖^2 := by
  classical
  let R := M.positiveColumnNorm τ a d (N + s)
  have hR : 0 ≤ R := M.positiveColumnNorm_nonneg τ a d (N + s)
  have hpos : (∑ j ∈ Finset.range (J + s + N + 1),
      ‖M.physicalMode a d j v‖^2) ≤ R^2 * ‖v‖^2 := by
    have he : (∑ j ∈ Finset.range (J + s + N + 1), ‖M.physicalMode a d j v‖^2) =
        ∑ j ∈ Finset.range (N + 1), ‖M.physicalMode a d j v‖^2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      rw [Q.physicalMode_zero_above_cutoff τ ha hv j (by
        simp only [Finset.mem_range] at hj; omega)]
      simp
    rw [he]
    apply (M.sum_positive_modes_sq_le τ a d hv).trans
    have hRN := M.positiveColumnNorm_nonneg τ a d N
    have hm := M.positiveColumnNorm_mono τ a d (show N ≤ N + s by omega)
    change M.positiveColumnNorm τ a d N ^ 2 * ‖v‖^2 ≤ _
    gcongr
  have hneg : (∑ j ∈ Finset.range s, ‖M.physicalMode a d ((j : ℤ) - s) v‖^2) ≤
      (s : ℝ) * (R^2 * ‖v‖^2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range s, R^2 * ‖v‖^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj := Finset.mem_range.mp hj
        have he : (j : ℤ) - s = -((s - j : ℕ) : ℤ) := by omega
        rw [he, ← mul_pow]
        have hn := (Q.negative_mode_norm_le_column τ ha hq hh hv (s - j)).trans
          (mul_le_mul_of_nonneg_right
            (M.positiveColumnNorm_mono τ a d (show N + (s - j) ≤ N + s by omega)) (norm_nonneg v))
        exact pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by simp
  calc
    _ ≤ ∑ j ∈ Finset.range (s + (J + s + N + 1)),
        ‖M.physicalMode a d ((j : ℤ) - s) v‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      positivity
    _ = (∑ j ∈ Finset.range s, ‖M.physicalMode a d ((j : ℤ) - s) v‖^2) +
        ∑ j ∈ Finset.range (J + s + N + 1), ‖M.physicalMode a d j v‖^2 := by
      rw [Finset.sum_range_add]
      simp only [Nat.cast_add, add_sub_cancel_left]
    _ ≤ (s : ℝ) * (R^2 * ‖v‖^2) + R^2 * ‖v‖^2 := add_le_add hneg hpos
    _ = _ := by dsimp [R]; ring

def adjointPhysicalMode (_Q : M.UnitaryStructure U) (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ W :=
  ((-1 : ℂ)^d) • ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
    M.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) (-m)

theorem adjointPhysicalMode_inner {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (m : ℤ) (v w : W) :
    inner ℂ (M.physicalMode a d m v) w = inner ℂ v (Q.adjointPhysicalMode a d m w) := by
  have h := Q.invariant d a ha (m + d - 1) v w
  refine h.trans ?_
  apply congrArg (fun x : W => inner ℂ v x)
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply congrArg (fun x : W => ((-1 : ℂ)^d) • x)
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  dsimp only [physicalMode]
  congr 2
  have hj := Finset.mem_range.mp hj
  omega

theorem adjointPhysicalMode_mem_cutoff (τ : EnergyBand) {a : V} {d N K : ℕ} (ha : a ∈ A.grade d)
    {v : W} (hv : v ∈ M.energyCutoff τ N) (m : ℤ) (hm : (N : ℤ) + m ≤ K) :
    Q.adjointPhysicalMode a d m v ∈ M.energyCutoff τ K := by
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Q.physicalMode_mem_cutoff τ
    (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j (by have := Finset.mem_range.mp hj; omega))
    hv (-m) (by omega)

theorem adjointPhysicalMode_zero_above_cutoff (τ : EnergyBand) {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : W} (hv : v ∈ M.energyCutoff τ N) (m : ℤ) (hm : (N : ℤ) < m) :
    Q.adjointPhysicalMode a d (-m) v = 0 := by
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply, neg_neg]
  have hs : (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
      M.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) m v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Q.physicalMode_zero_above_cutoff τ
      (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j (by have := Finset.mem_range.mp hj; omega))
      hv m hm, smul_zero]
  rw [hs, smul_zero]

theorem adjointPhysicalMode_eq {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) :
    Q.adjointPhysicalMode a d m = M.physicalMode a d (-m) := by
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [← Q.adjointPhysicalMode_inner ha, Q.physicalMode_adjoint ha hq hh]

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
