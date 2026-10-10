import OAI.RepresentationTheory.VertexAlgebra.ModuleBands

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
def modeBlock (t : EnergyBand) (a : V) (d h k : ℕ) : M.bandGrade t h →L[ℂ] W := by
  exact LinearMap.toContinuousLinearMap
    ((M.physicalMode a d ((h : ℤ) - k)).domRestrict (M.bandGrade t h))

@[simp]
theorem modeBlock_apply (t : EnergyBand) (a : V) (d h k : ℕ) (c : M.bandGrade t h) :
    M.modeBlock t a d h k c = M.physicalMode a d ((h : ℤ) - k) c := rfl

 

def BlockControl (t : EnergyBand) (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ h ≤ N, ∀ k ≤ N, ∀ c ∈ M.bandGrade t h,
    ‖M.physicalMode a d ((h : ℤ) - k) c‖ ≤ K * ‖c‖

variable {t : EnergyBand}

theorem blockControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : M.BlockControl t a d N K) (hKL : K ≤ L) : M.BlockControl t a d N L := by
  intro h hh k hk c hc
  exact (H h hh k hk c hc).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem blockControl_zero (d N : ℕ) : M.BlockControl t 0 d N 0 := by
  intro h hh k hk c hc
  simp [physicalMode]

theorem blockControl_add {a b : V} {d N : ℕ} {K L : ℝ}
    (ha : M.BlockControl t a d N K) (hb : M.BlockControl t b d N L) :
    M.BlockControl t (a + b) d N (K + L) := by
  intro h hh k hk c hc
  change ‖(mode M.fields (a + b) _) c‖ ≤ _
  rw [mode_add, LinearMap.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (ha h hh k hk c hc) (hb h hh k hk c hc))

theorem blockControl_smul {a : V} {d N : ℕ} {K : ℝ}
    (ha : M.BlockControl t a d N K) (z : ℂ) :
    M.BlockControl t (z • a) d N (‖z‖ * K) := by
  intro h hh k hk c hc
  change ‖(mode M.fields (z • a) _) c‖ ≤ _
  rw [mode_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (ha h hh k hk c hc) (norm_nonneg _)

variable {M} (Q : M.UnitaryStructure U)
include Q

theorem normalProduct_blockControl {a b : V} {d e N : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    {K L R : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : M.BlockControl t a d N K) (Hb : M.BlockControl t b e N L)
    (Hsing : ∀ j < d - 1, M.BlockControl t (mode A.fields a j b) (d + e - j - 1) N R) :
    M.BlockControl t (mode A.fields a (-1) b) (d + e) N
      (((2 : ℝ) * N + 1) * K * L + correctionMass d * R) := by
  classical
  intro h hh k hk c hc
  let f : ℕ → W := fun j => M.physicalMode a d (-1 - j)
    (M.physicalMode b e ((h : ℤ) - k + 1 + j) c)
  let g : ℕ → W := fun j => M.physicalMode b e ((h : ℤ) - k - j)
    (M.physicalMode a d j c)
  let r : ℕ → ℕ → W := fun i j => (i.choose j : ℂ) •
    mode M.fields (mode A.fields a j b) ((h : ℤ) - k + d + e - 2 - j) c
  have hf (j : ℕ) (hj : j ∈ Finset.range k) : ‖f j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := k - 1 - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = (h : ℤ) - k + 1 + j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = -1 - j := by dsimp [l]; omega
    have hx : M.physicalMode b e ((h : ℤ) - k + 1 + j) c ∈ M.bandGrade t l :=
      M.mode_mem_band t hb hc _ (by dsimp [l]; omega)
    have H₁ := Ha l hl k hk _ hx
    have H₂ := Hb h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖f j‖ ≤ K * ‖M.physicalMode b e ((h : ℤ) - k + 1 + j) c‖ := H₁
      _ ≤ K * (L * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hK
      _ = _ := by ring
  have hg (j : ℕ) (hj : j ∈ Finset.range (h + 1)) : ‖g j‖ ≤ K * L * ‖c‖ := by
    simp only [Finset.mem_range] at hj
    let l := h - j
    have hl : l ≤ N := by dsimp [l]; omega
    have hidx : (h : ℤ) - l = j := by dsimp [l]; omega
    have hidx' : (l : ℤ) - k = (h : ℤ) - k - j := by dsimp [l]; omega
    have hx : M.physicalMode a d j c ∈ M.bandGrade t l :=
      M.mode_mem_band t ha hc _ (by dsimp [l]; omega)
    have H₁ := Hb l hl k hk _ hx
    have H₂ := Ha h hh l hl c hc
    rw [hidx'] at H₁
    rw [hidx] at H₂
    calc
      ‖g j‖ ≤ L * ‖M.physicalMode a d j c‖ := H₁
      _ ≤ L * (K * ‖c‖) := mul_le_mul_of_nonneg_left H₂ hL
      _ = _ := by ring
  have hr (i : ℕ) (hi : i ∈ Finset.range (d - 1))
      (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : ‖r i j‖ ≤ (i.choose j : ℝ) * R * ‖c‖ := by
    simp only [Finset.mem_range] at hi hj
    have hjs : j < d - 1 := by omega
    have H := Hsing j hjs h hh k hk c hc
    have he : (h : ℤ) - k + (d + e - j - 1 : ℕ) - 1 =
        (h : ℤ) - k + d + e - 2 - j := by omega
    simp only [physicalMode, he] at H
    dsimp only [r]
    rw [norm_smul, Complex.norm_natCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)
  have hfs : ‖∑ j ∈ Finset.range k, f j‖ ≤ (k : ℝ) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      norm_sum_le_of_le (Finset.range k) hf
  have hgs : ‖∑ j ∈ Finset.range (h + 1), g j‖ ≤ ((h : ℝ) + 1) * (K * L * ‖c‖) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      norm_sum_le_of_le (Finset.range (h + 1)) hg
  have hrs : ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ ≤
      correctionMass d * R * ‖c‖ := by
    have H := norm_sum_le_of_le (Finset.range (d - 1)) (fun i hi =>
      norm_sum_le_of_le (Finset.range (i + 1)) (hr i hi))
    simpa only [correctionMass, Finset.sum_mul] using H
  rw [Q.physical_normal_product_on_band t ha hb hc hd k]
  change ‖(∑ j ∈ Finset.range k, f j) + (∑ j ∈ Finset.range (h + 1), g j) -
    (∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j)‖ ≤ _
  calc
    _ ≤ ‖∑ j ∈ Finset.range k, f j‖ + ‖∑ j ∈ Finset.range (h + 1), g j‖ +
        ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1), r i j‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (k : ℝ) * (K * L * ‖c‖) + ((h : ℝ) + 1) * (K * L * ‖c‖) +
        correctionMass d * R * ‖c‖ := add_le_add (add_le_add hfs hgs) hrs
    _ = ((h : ℝ) + k + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by ring
    _ ≤ ((2 : ℝ) * N + 1) * (K * L * ‖c‖) + correctionMass d * R * ‖c‖ := by
      have hcount : (h : ℝ) + k + 1 ≤ (2 : ℝ) * N + 1 := by
        exact_mod_cast (show h + k + 1 ≤ 2 * N + 1 by omega)
      gcongr
    _ = _ := by ring

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
