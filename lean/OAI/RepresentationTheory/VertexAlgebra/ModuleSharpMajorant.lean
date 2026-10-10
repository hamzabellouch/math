import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpGrowth

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
theorem homogeneousC2_le_sharpDegreeGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, M.SharpGrowth X a d) :
    A.homogeneousC2 w ≤ M.sharpDegreeGrowthSubmodule X w (w-1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change M.SharpDegreeGrowth X (mode A.fields a (-2) b) w (w-1)
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := M.translation_sharpDegreeGrowth hX ha (hprev d (by omega) a ha)
    rw [hweight']
    change M.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) (d+1-1)
    simpa only [Nat.add_sub_cancel] using
      (show M.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) d from
        ⟨M.columnGrowth_smul H.1 z, M.zeroGrowth_smul H.2 z⟩)
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [mode_smul, LinearMap.smul_apply, A.vacuum_mode]
    norm_num
    exact ⟨M.columnGrowth_zero X _ _ _, M.zeroGrowth_zero X _ _ _⟩
  have hTa : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  have Ha := Q.bothSharpColumnGrowth hX ha
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HT := Q.translation_bothColumnGrowth hX ha Ha
  have hpexp : (2*d-1)+2 = 2*(d+1)-1 := by omega
  rw [hpexp] at HT
  have HB := Q.bothSharpColumnGrowth hX hb
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HS : ∀ j < (d+1)-1,
      M.ColumnGrowth X (mode A.fields (A.toVertexAlgebra.translation a) j b)
        (d+1+e-j-1) (2*(d+1+e)-2) (2*(d+e)) := by
    intro j hj
    have hgrade := A.mode_mem_grade hTa hb (j : ℤ)
      (k := d+1+e-j-1) (by omega)
    exact M.columnGrowth_mono hX (hprev _ (by omega) _ hgrade).1 (by omega) (by omega)
  have H := Q.normalProduct_degreeGrowth hX hTa hb (by omega) (by omega) HT HB HS
  have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b = mode A.fields a (-2) b := by
    rw [A.translation_covariance]
    norm_num
  rw [heq] at H
  convert H using 1 <;> omega

 

theorem grade_sharpGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      M.SharpGrowth X a d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, M.SharpGrowth X a d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨M.columnGrowth_smul (M.vacuum_sharpGrowth X hX).1 z,
        M.zeroGrowth_smul (M.vacuum_sharpGrowth X hX).2 z⟩
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      have H := M.translation_sharpGrowth hX hb (ih e (by omega) b hb)
      have Q := hsmall _ (by omega) hdD q hq hqq
      exact ⟨M.columnGrowth_add Q.1 H.1, M.zeroGrowth_add Q.2 H.2⟩
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact M.sharpDegreeGrowth_mono hX
        (Q.homogeneousC2_le_sharpDegreeGrowth hX d ih hc) (by omega)

end UnitaryStructure
variable (τ : EnergyBand)
def zeroModeOnCutoff (a : V) (d N : ℕ) : M.energyCutoff τ N →L[ℂ] W :=
  LinearMap.toContinuousLinearMap ((M.physicalMode a d 0).comp (M.energyCutoff τ N).subtype)

def zeroModeCutoffNorm (a : V) (d N : ℕ) : ℝ := ‖M.zeroModeOnCutoff τ a d N‖

theorem zeroMode_norm_le (a : V) (d : ℕ) {N : ℕ} {v : W} (hv : v ∈ M.energyCutoff τ N) :
    ‖M.physicalMode a d 0 v‖ ≤ M.zeroModeCutoffNorm τ a d N * ‖v‖ :=
  (M.zeroModeOnCutoff τ a d N).le_opNorm ⟨v, hv⟩

theorem zeroModeCutoffNorm_mono (a : V) (d : ℕ) : Monotone (M.zeroModeCutoffNorm τ a d) := by
  intro N K hNM
  change ‖M.zeroModeOnCutoff τ a d N‖ ≤ ‖M.zeroModeOnCutoff τ a d K‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (M.zeroModeOnCutoff τ a d K))
  intro v
  exact M.zeroMode_norm_le τ a d (M.energyCutoff_mono τ hNM v.property)

 

def sharpColumnQuantity (a : V) (d N : ℕ) : ℝ :=
  M.positiveColumnNorm τ a d N ^ 2 / (N+1 : ℝ)^(2*d-1)

def sharpZeroQuantity (a : V) (d N : ℕ) : ℝ :=
  M.zeroModeCutoffNorm τ a d N ^ 2 / (N+1 : ℝ)^(max 1 (2*d-2))

def rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((M.sharpColumnQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (M.sharpZeroQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹)

 

def sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (M.rawSharpMajorant τ D S)

theorem sharpColumnQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ M.sharpColumnQuantity τ a d N := by
  unfold sharpColumnQuantity
  positivity

theorem sharpZeroQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ M.sharpZeroQuantity τ a d N := by
  unfold sharpZeroQuantity
  positivity

theorem one_le_rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ M.rawSharpMajorant τ D S N := by
  unfold rawSharpMajorant
  have H : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((M.sharpColumnQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (M.sharpZeroQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro a _
    exact add_nonneg (Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ a d N) _)
      (Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ a d N) _)
  linarith

theorem rawSharpMajorant_le (D : ℕ) (S : ℕ → Finset V) {N K : ℕ} (hNM : N ≤ K) :
    M.rawSharpMajorant τ D S N ≤ M.sharpMajorant τ D S K := by
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem one_le_sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ M.sharpMajorant τ D S N :=
  (M.one_le_rawSharpMajorant τ D S N).trans (M.rawSharpMajorant_le τ D S le_rfl)

theorem sharpMajorant_mono (D : ℕ) (S : ℕ → Finset V) : Monotone (M.sharpMajorant τ D S) := by
  intro N K hNM
  apply Finset.sup'_le
  intro k hk
  exact M.rawSharpMajorant_le τ D S (by have := Finset.mem_range.mp hk; omega)

theorem root_sharpQuantity_le (D : ℕ) (S : ℕ → Finset V) {N d : ℕ} {a : V}
    (hd : d ≤ D) (ha : a ∈ S d) :
    (M.sharpColumnQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ M.sharpMajorant τ D S N ∧
    (M.sharpZeroQuantity τ a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ M.sharpMajorant τ D S N := by
  let F (e : ℕ) (b : V) := (M.sharpColumnQuantity τ b e N)^((2*e : ℕ) : ℝ)⁻¹ +
     (M.sharpZeroQuantity τ b e N)^((2*e : ℕ) : ℝ)⁻¹
  have hF (e : ℕ) (b : V) : 0 ≤ F e b :=
    add_nonneg (Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ b e N) _)
      (Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ b e N) _)
  have H₁ := Finset.single_le_sum (fun b _ => hF d b) ha
  have H₂ := Finset.single_le_sum (s := Finset.range (D+1)) (a := d) (f := fun e => ∑ b ∈ S e, F e b)
    (fun e _ => Finset.sum_nonneg (fun b _ => hF e b)) (Finset.mem_range.mpr (by omega))
  have H₃ : F d a ≤ M.sharpMajorant τ D S N := by
    apply (H₁.trans H₂).trans
    exact (le_add_of_nonneg_left zero_le_one).trans (M.rawSharpMajorant_le τ D S le_rfl)
  constructor
  · exact (le_add_of_nonneg_right (Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ a d N) _)).trans H₃
  · exact (le_add_of_nonneg_left (Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ a d N) _)).trans H₃

theorem generator_sharpGrowth (D : ℕ) (S : ℕ → Finset V) {d : ℕ} {a : V}
    (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    M.SharpGrowth (fun τ => M.sharpMajorant τ D S) a d := by
  have hquant (τ : EnergyBand) (N : ℕ) : M.sharpColumnQuantity τ a d N ≤ M.sharpMajorant τ D S N^(2*d) ∧
      M.sharpZeroQuantity τ a d N ≤ M.sharpMajorant τ D S N^(2*d) := by
    obtain ⟨H, K⟩ := M.root_sharpQuantity_le τ D S hD ha (N := N)
    have H' := pow_le_pow_left₀ (Real.rpow_nonneg (M.sharpColumnQuantity_nonneg τ a d N) _) H (2*d)
    have K' := pow_le_pow_left₀ (Real.rpow_nonneg (M.sharpZeroQuantity_nonneg τ a d N) _) K (2*d)
    rw [Real.rpow_inv_natCast_pow (M.sharpColumnQuantity_nonneg τ a d N) (by omega)] at H'
    rw [Real.rpow_inv_natCast_pow (M.sharpZeroQuantity_nonneg τ a d N) (by omega)] at K'
    exact ⟨H', K'⟩
  constructor
  · refine ⟨1, zero_le_one, ?_⟩
    intro τ N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mp (hquant τ N).1
    apply (M.sum_positive_modes_sq_le τ a d hv).trans
    simpa only [one_mul, mul_comm (M.sharpMajorant τ D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)
  · refine ⟨1, zero_le_one, ?_⟩
    intro τ N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(max 1 (2*d-2)))).mp (hquant τ N).2
    have Z := pow_le_pow_left₀ (norm_nonneg _) (M.zeroMode_norm_le τ a d hv) 2
    rw [mul_pow] at Z
    apply Z.trans
    simpa only [one_mul, mul_comm (M.sharpMajorant τ D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem exists_sharpMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
        a ∈ Submodule.span ℂ (S d : Set V)) ∧
      (∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) ∧
      (∀ w, ∀ a ∈ A.grade w, M.SharpGrowth (fun τ => M.sharpMajorant τ D S) a w) := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  have hspanS (d : ℕ) (hd : 1 ≤ d) (hdD : d ≤ D) (a : V) (ha : a ∈ A.grade d)
      (hq : A.IsQuasiPrimary a) : a ∈ Submodule.span ℂ (S d : Set V) := by
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    rw [he]
    exact hspan d a ha hq
  refine ⟨D, hD, S, ?_, hS, hspanS, hcut, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply Q.grade_sharpGrowth (fun τ => M.one_le_sharpMajorant τ D S) D _ hcut
    intro d hd hdD a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        M.sharpGrowthSubmodule (fun τ => M.sharpMajorant τ D S) d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact M.generator_sharpGrowth D S (by omega) hdD hb
    exact hle (hspanS d hd hdD a ha hq)

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
