import OAI.RepresentationTheory.VertexAlgebra.ModuleBlockGrowth

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
def generatorMajorant (D : ℕ) (S : ℕ → Finset V) (t : EnergyBand) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
    ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ‖M.modeBlock t a d h k‖ ^ (d : ℝ)⁻¹

theorem one_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V) (t : EnergyBand) (N : ℕ) :
    1 ≤ M.generatorMajorant D S t N := by
  dsimp [generatorMajorant]
  have : 0 ≤ ∑ d ∈ Finset.range (D + 1), ∑ a ∈ S d,
      ∑ h ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ‖M.modeBlock t a d h k‖ ^ (d : ℝ)⁻¹ := by
    positivity
  linarith

theorem root_modeBlock_le_generatorMajorant (D : ℕ) (S : ℕ → Finset V) (t : EnergyBand)
    {d h k N : ℕ} {a : V} (hd : d ≤ D) (ha : a ∈ S d)
    (hh : h ≤ N) (hk : k ≤ N) :
    ‖M.modeBlock t a d h k‖ ^ (d : ℝ)⁻¹ ≤ M.generatorMajorant D S t N := by
  have H (e : ℕ) (b : V) (i j : ℕ) :
      0 ≤ ‖M.modeBlock t b e i j‖ ^ (e : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (M.modeBlock t b e i j)) _
  have Hk (e : ℕ) (b : V) (i : ℕ) : 0 ≤
      ∑ j ∈ Finset.range (N + 1), ‖M.modeBlock t b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun j _ => H e b i j)
  have Hh (e : ℕ) (b : V) : 0 ≤
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖M.modeBlock t b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun i _ => Hk e b i)
  have Ha (e : ℕ) : 0 ≤ ∑ b ∈ S e,
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        ‖M.modeBlock t b e i j‖ ^ (e : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun b _ => Hh e b)
  have h₁ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
    (fun j _ => H d a h j) (Finset.mem_range.mpr (by omega))
  have h₂ := Finset.single_le_sum (s := Finset.range (N + 1)) (a := h)
    (fun i _ => Hk d a i) (Finset.mem_range.mpr (by omega))
  have h₃ := Finset.single_le_sum (s := S d) (a := a) (fun b _ => Hh d b) ha
  have h₄ := Finset.single_le_sum (s := Finset.range (D + 1)) (a := d)
    (fun e _ => Ha e) (Finset.mem_range.mpr (by omega))
  exact (h₁.trans (h₂.trans (h₃.trans h₄))).trans (le_add_of_nonneg_left zero_le_one)

theorem generator_blockGrowth (D : ℕ) (S : ℕ → Finset V)
    {d : ℕ} {a : V} (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    M.BlockGrowth (M.generatorMajorant D S) a d d := by
  refine ⟨1, zero_le_one, 0, fun t N h hh k hk c hc => ?_⟩
  have hnorm := M.root_modeBlock_le_generatorMajorant D S t hD ha hh hk
  have ht : 0 ≤ ‖M.modeBlock t a d h k‖ ^ (d : ℝ)⁻¹ :=
    Real.rpow_nonneg (norm_nonneg (M.modeBlock t a d h k)) _
  have hpow := pow_le_pow_left₀ ht hnorm d
  rw [Real.rpow_inv_natCast_pow (x := ‖M.modeBlock t a d h k‖) (n := d)
    (norm_nonneg (M.modeBlock t a d h k)) (by omega)] at hpow
  have h := (M.modeBlock t a d h k).le_opNorm (⟨c, hc⟩ : M.bandGrade t h)
  simpa only [pow_zero, mul_one, one_mul, modeBlock_apply, ← Submodule.norm_coe] using
    h.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg c))

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
