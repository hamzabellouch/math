import OAI.RepresentationTheory.VertexAlgebra.ModuleBlockControl

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
 

def BlockGrowth (B : EnergyBand → ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t N,
    M.BlockControl t a d N (C * (1 + (N : ℝ)) ^ p * B t N ^ w)

theorem blockGrowth_zero (B : EnergyBand → ℕ → ℝ) (d w : ℕ) : M.BlockGrowth B 0 d w := by
  refine ⟨0, le_rfl, 0, ?_⟩
  intro t N
  simpa only [zero_mul] using M.blockControl_zero d N

theorem blockGrowth_add {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N) {a b : V} {d w : ℕ}
    (ha : M.BlockGrowth B a d w) (hb : M.BlockGrowth B b d w) :
    M.BlockGrowth B (a + b) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  obtain ⟨D, hD, q, hq⟩ := hb
  refine ⟨C + D, add_nonneg hC hD, p + q, fun t N => ?_⟩
  apply M.blockControl_mono (M.blockControl_add (hp t N) (hq t N))
  have hBN : 0 ≤ B t N := (zero_le_one.trans (hB t N))
  have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ ≤ C * (1 + (N : ℝ)) ^ (p + q) * B t N ^ w +
        D * (1 + (N : ℝ)) ^ (p + q) * B t N ^ w := by gcongr
    _ = _ := by ring

theorem blockGrowth_smul {B : EnergyBand → ℕ → ℝ} {a : V} {d w : ℕ}
    (ha : M.BlockGrowth B a d w) (z : ℂ) : M.BlockGrowth B (z • a) d w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC, p, fun t N => ?_⟩
  simpa only [mul_assoc] using M.blockControl_smul (hp t N) z

theorem blockGrowth_mono_weight {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {a : V} {d w w' : ℕ} (ha : M.BlockGrowth B a d w) (hw : w ≤ w') :
    M.BlockGrowth B a d w' := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨C, hC, p, fun t N => ?_⟩
  apply M.blockControl_mono (hp t N)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB t N) hw) (by positivity)

 

theorem translation_blockGrowth {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {a : V} {d w : ℕ} (ha : M.BlockGrowth B a d w) :
    M.BlockGrowth B (A.toVertexAlgebra.translation a) (d + 1) w := by
  obtain ⟨C, hC, p, hp⟩ := ha
  refine ⟨((d : ℝ) + 2) * C, by positivity, p + 1, ?_⟩
  intro t N h hh k hk c hc
  have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
  have he (m : ℤ) : M.physicalMode (A.toVertexAlgebra.translation a) (d + 1) m =
      (-(m + (d : ℤ) : ℤ) : ℂ) • M.physicalMode a d m := by
    simp only [physicalMode, Nat.cast_add, Nat.cast_one]
    rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, M.toWeakModule.translation_covariance]
  rw [he, LinearMap.smul_apply, norm_smul]
  have hcoef : ‖(-((h : ℤ) - k + d) : ℤ)‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simp only [Int.norm_eq_abs, Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_natCast, abs_neg]
    rw [abs_le]
    constructor <;> nlinarith [show (h : ℝ) ≤ N by exact_mod_cast hh,
      show (k : ℝ) ≤ N by exact_mod_cast hk, Nat.cast_nonneg (α := ℝ) h,
      Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) d,
      Nat.cast_nonneg (α := ℝ) N]
  have hcoef' : ‖(-(((h : ℤ) - k + d : ℤ) : ℂ))‖ ≤ ((d : ℝ) + 2) * (1 + (N : ℝ)) := by
    simpa only [norm_neg, Complex.norm_intCast, Int.norm_eq_abs, Int.cast_neg, abs_neg] using hcoef
  calc
    _ ≤ (((d : ℝ) + 2) * (1 + (N : ℝ))) *
        (C * (1 + (N : ℝ)) ^ p * B t N ^ w * ‖c‖) := by
      exact mul_le_mul hcoef' (hp t N h hh k hk c hc) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

 

theorem finite_blockGrowth_uniform {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d w : ι → ℕ)
    (hg : ∀ i ∈ s, M.BlockGrowth B (a i) (d i) (w i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i ∈ s, ∀ t N,
      M.BlockControl t (a i) (d i) N (C * (1 + (N : ℝ)) ^ p * B t N ^ w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, p, hp⟩ := hg i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, q, hq⟩ := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, p + q, ?_⟩
    intro j hj t N
    have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
    have hNp : (1 + (N : ℝ)) ^ p ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    have hNq : (1 + (N : ℝ)) ^ q ≤ (1 + (N : ℝ)) ^ (p + q) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply M.blockControl_mono (hp t N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply M.blockControl_mono (hq j hj t N)
      gcongr
      exact le_add_of_nonneg_left hC

 

theorem normalProduct_blockGrowth (Q : M.UnitaryStructure U) {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (Ha : M.BlockGrowth B a d d) (Hb : M.BlockGrowth B b e e)
    (Hsing : ∀ j < d - 1,
      M.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e - j - 1)) :
    M.BlockGrowth B (mode A.fields a (-1) b) (d + e) (d + e) := by
  classical
  obtain ⟨C, hC, p, hp⟩ := Ha
  obtain ⟨D, hD, q, hq⟩ := Hb
  have hsG : ∀ j ∈ Finset.range (d - 1),
      M.BlockGrowth B (mode A.fields a j b) (d + e - j - 1) (d + e) := by
    intro j hj
    exact M.blockGrowth_mono_weight hB (Hsing j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨R, hR, s, hs⟩ := M.finite_blockGrowth_uniform hB (Finset.range (d - 1))
    (fun j => mode A.fields a j b) (fun j => d + e - j - 1) (fun _ => d + e) hsG
  refine ⟨2 * C * D + correctionMass d * R,
    add_nonneg (by positivity) (mul_nonneg (correctionMass_nonneg d) hR), p + q + s + 1, ?_⟩
  intro t N
  have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
  have hmass := correctionMass_nonneg d
  apply M.blockControl_mono (normalProduct_blockControl Q ha hb hd
    (by positivity) (by positivity) (hp t N) (hq t N)
    (fun j hj => hs j (Finset.mem_range.mpr hj) t N))
  have hpow₁ : (1 + (N : ℝ)) ^ (p + q + 1) ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  have hpow₂ : (1 + (N : ℝ)) ^ s ≤ (1 + (N : ℝ)) ^ (p + q + s + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
  calc
    _ = ((2 : ℝ) * N + 1) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B t N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B t N ^ (d + e) := by
      simp only [pow_add]
      ring
    _ ≤ (2 * (1 + (N : ℝ))) * (C * D * (1 + (N : ℝ)) ^ (p + q) * B t N ^ (d + e)) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B t N ^ (d + e) := by
      gcongr
      linarith
    _ = 2 * C * D * (1 + (N : ℝ)) ^ (p + q + 1) * B t N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ s * B t N ^ (d + e) := by
      rw [pow_succ]
      ring
    _ ≤ 2 * C * D * (1 + (N : ℝ)) ^ (p + q + s + 1) * B t N ^ (d + e) +
        correctionMass d * R * (1 + (N : ℝ)) ^ (p + q + s + 1) * B t N ^ (d + e) := by
      gcongr
    _ = _ := by ring

 

def blockGrowthSubmodule (B : EnergyBand → ℕ → ℝ) (hB : ∀ t N, 1 ≤ B t N) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | M.BlockGrowth B a d w}
  zero_mem' := M.blockGrowth_zero B d w
  add_mem' := M.blockGrowth_add hB
  smul_mem' z _ h := M.blockGrowth_smul h z

 
theorem vacuum_blockGrowth (B : EnergyBand → ℕ → ℝ) : M.BlockGrowth B A.vacuum 0 0 := by
  refine ⟨1, zero_le_one, 0, fun t N h hh k hk c hc => ?_⟩
  simp only [physicalMode, Nat.cast_zero, add_zero, M.toWeakModule.vacuum_mode, pow_zero, mul_one, one_mul]
  split_ifs <;> simp

 

theorem homogeneousC2_le_blockGrowth (Q : M.UnitaryStructure U) {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, M.BlockGrowth B a d d) :
    A.homogeneousC2 w ≤ M.blockGrowthSubmodule B hB w w := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change M.BlockGrowth B (mode A.fields a (-2) b) w w
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := M.translation_blockGrowth hB (hprev d (by omega) a ha)
    have H' := M.blockGrowth_mono_weight hB H (show d ≤ w by omega)
    rw [hweight'] at H' ⊢
    exact M.blockGrowth_smul H' z
  · have hepos : 1 ≤ e := by omega
    have hTgrade : A.toVertexAlgebra.translation a ∈ A.grade (d + 1) := by
      rw [← A.virasoro_neg_one_eq_translation]
      exact A.virasoro_mem_grade ha (-1) (by omega)
    have hT := hprev (d + 1) (by omega) (A.toVertexAlgebra.translation a) hTgrade
    have hB' := hprev e (by omega) b hb
    have hsing : ∀ j < (d + 1) - 1,
        M.BlockGrowth B (mode A.fields (A.toVertexAlgebra.translation a) j b)
          (d + 1 + e - j - 1) (d + 1 + e - j - 1) := by
      intro j hj
      apply hprev _ (by omega)
      exact A.mode_mem_grade hTgrade hb j (by omega)
    have H := M.normalProduct_blockGrowth Q hB hTgrade hb (by omega) hT hB' hsing
    have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b =
        mode A.fields a (-2) b := by
      rw [A.translation_covariance]
      norm_num
    rw [heq, show d + 1 + e = w by omega] at H
    exact H

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
