import OAI.RepresentationTheory.VertexAlgebra.ModuleSharpNormalProducts

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
def ColumnGrowth (X : EnergyBand → ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N, M.ColumnControl τ a d N (C * (N + 1 : ℝ)^p * X τ N^q)

 

def ZeroGrowth (X : EnergyBand → ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N v, v ∈ M.energyCutoff τ N →
    ‖M.physicalMode a d 0 v‖^2 ≤ C * (N + 1 : ℝ)^p * X τ N^q * ‖v‖^2

theorem columnGrowth_zero (X : EnergyBand → ℕ → ℝ) (d p q : ℕ) : M.ColumnGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro τ N v hv
  simp [physicalMode, mode_zero]

theorem zeroGrowth_zero (X : EnergyBand → ℕ → ℝ) (d p q : ℕ) : M.ZeroGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro τ N v hv
  simp [physicalMode, mode_zero]

theorem columnGrowth_add {X : EnergyBand → ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : M.ColumnGrowth X a d p q) (Hb : M.ColumnGrowth X b d p q) :
    M.ColumnGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro τ N v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 2 * (‖M.physicalMode a d m v‖^2 + ‖M.physicalMode b d m v‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      simp only [physicalMode, mode_add, LinearMap.add_apply]
      exact SharpColumns.norm_add_sq_le_two _ _
    _ = 2 * ((∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2) +
        ∑ m ∈ Finset.range (N + 1), ‖M.physicalMode b d m v‖^2) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by nlinarith [HC τ N v hv, HD τ N v hv]

theorem zeroGrowth_add {X : EnergyBand → ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : M.ZeroGrowth X a d p q) (Hb : M.ZeroGrowth X b d p q) :
    M.ZeroGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro τ N v hv
  have h := SharpColumns.norm_add_sq_le_two (M.physicalMode a d 0 v) (M.physicalMode b d 0 v)
  simp only [physicalMode, mode_add, LinearMap.add_apply]
  dsimp only [physicalMode] at h HC HD
  nlinarith [HC τ N v hv, HD τ N v hv]

theorem columnGrowth_smul {X : EnergyBand → ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : M.ColumnGrowth X a d p q) (z : ℂ) : M.ColumnGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro τ N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    ← Finset.mul_sum, mul_assoc] using mul_le_mul_of_nonneg_left (HC τ N v hv) (sq_nonneg ‖z‖)

theorem zeroGrowth_smul {X : EnergyBand → ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : M.ZeroGrowth X a d p q) (z : ℂ) : M.ZeroGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro τ N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    mul_assoc] using mul_le_mul_of_nonneg_left (HC τ N v hv) (sq_nonneg ‖z‖)

theorem columnGrowth_mono {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d p q p' q' : ℕ}
    (H : M.ColumnGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    M.ColumnGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, fun τ N => M.columnControl_mono τ (HC τ N) ?_⟩
  have hXN := zero_le_one.trans (hX τ N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX τ N

theorem zeroGrowth_mono {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d p q p' q' : ℕ}
    (H : M.ZeroGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    M.ZeroGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro τ N v hv
  apply (HC τ N v hv).trans
  have hXN := zero_le_one.trans (hX τ N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX τ N

theorem zeroGrowth_of_columnGrowth {X : EnergyBand → ℕ → ℝ} {a : V} {d p q : ℕ}
    (_ha : a ∈ A.grade d) (H : M.ColumnGrowth X a d p q) : M.ZeroGrowth X a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  exact ⟨C, hC, fun τ N v hv => (Finset.single_le_sum (f := fun m : ℕ => ‖M.physicalMode a d m v‖^2) (fun _ _ => sq_nonneg _) (by simp : 0 ∈ Finset.range (N+1))).trans (HC τ N v hv)⟩

 

def SharpDegreeGrowth (X : EnergyBand → ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  M.ColumnGrowth X a d (2*d-1) (2*w) ∧ M.ZeroGrowth X a d (max 1 (2*d-2)) (2*w)

def SharpGrowth (X : EnergyBand → ℕ → ℝ) (a : V) (d : ℕ) : Prop :=
  M.SharpDegreeGrowth X a d d

def sharpGrowthSubmodule (X : EnergyBand → ℕ → ℝ) (d : ℕ) : Submodule ℂ V where
  carrier := {a | M.SharpGrowth X a d}
  zero_mem' := ⟨M.columnGrowth_zero X d _ _, M.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨M.columnGrowth_add h.1 k.1, M.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨M.columnGrowth_smul h.1 z, M.zeroGrowth_smul h.2 z⟩

theorem finite_columnGrowth_uniform {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, M.ColumnGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ τ N,
      M.ColumnControl τ (a i) (d i) N (C * (N + 1 : ℝ)^p * X τ N^q) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj τ N
    have hXN := zero_le_one.trans (hX τ N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply M.columnControl_mono τ (HC τ N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply M.columnControl_mono τ (HD j hj τ N)
      gcongr
      exact le_add_of_nonneg_left hC

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem adjointColumnControl_of_columns (τ : EnergyBand) {a : V} {d N : ℕ} {R : ℝ}
    (H : ∀ j ≤ d, M.ColumnControl τ ((A.virasoroMode 1^j) (U.pct a)) (d-j) N R) :
    Q.AdjointColumnControl τ a d N (CFTTypeVOA.UnitaryStructure.adjointMass d * R) := by
  intro v hv
  let T := fun j m : ℕ => (j.factorial : ℂ)⁻¹ •
    M.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) m v
  have hT (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖T j m‖^2) ≤ ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2 := by
    have H' := H j (by have := Finset.mem_range.mp hj; omega) v hv
    simpa only [T, norm_smul, mul_pow, ← Finset.mul_sum, mul_assoc] using
      mul_le_mul_of_nonneg_left H' (sq_nonneg ‖(j.factorial : ℂ)⁻¹‖)
  have h := SharpColumns.sum_columns_sq_le (Finset.range (d + 1)) (Finset.range (N + 1))
    T (fun j => ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2) hT
  simpa only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    neg_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    CFTTypeVOA.UnitaryStructure.adjointMass, Finset.card_range, Nat.cast_add, Nat.cast_one, Finset.sum_mul, mul_assoc, T] using h

 

theorem bothColumnGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d p q : ℕ}
    (Ha : M.ColumnGrowth X a d p q)
    (H : ∀ j ≤ d, M.ColumnGrowth X ((A.virasoroMode 1^j) (U.pct a)) (d-j) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ a d N (C * (N + 1 : ℝ)^p * X τ N^q) ∧
      Q.AdjointColumnControl τ a d N (C * (N + 1 : ℝ)^p * X τ N^q) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨R, hR, HR⟩ := M.finite_columnGrowth_uniform hX (Finset.range (d + 1))
    (fun j => (A.virasoroMode 1^j) (U.pct a)) (fun j => d-j) p q
    (fun j hj => H j (by have := Finset.mem_range.mp hj; omega))
  refine ⟨C + CFTTypeVOA.UnitaryStructure.adjointMass d * R, add_nonneg hC (mul_nonneg (CFTTypeVOA.UnitaryStructure.adjointMass_nonneg d) hR), ?_⟩
  intro τ N
  have hXN := zero_le_one.trans (hX τ N)
  have hM := CFTTypeVOA.UnitaryStructure.adjointMass_nonneg d
  constructor
  · apply M.columnControl_mono τ (HC τ N)
    gcongr
    exact le_add_of_nonneg_right (mul_nonneg hM hR)
  · intro v hv
    have H' := Q.adjointColumnControl_of_columns τ
      (fun j hj => HR j (Finset.mem_range.mpr (by omega)) τ N) v hv
    apply H'.trans
    calc
      _ = (CFTTypeVOA.UnitaryStructure.adjointMass d * R) * (N + 1 : ℝ)^p * X τ N^q * ‖v‖^2 := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left hC

theorem bothSharpColumnGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∀ e ≤ d, ∀ b ∈ A.grade e, M.ColumnGrowth X b e (2*e-1) (2*e)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ a d N (C * (N + 1 : ℝ)^(2*d-1) * X τ N^(2*d)) ∧
      Q.AdjointColumnControl τ a d N (C * (N + 1 : ℝ)^(2*d-1) * X τ N^(2*d)) := by
  apply Q.bothColumnGrowth hX (H d le_rfl a ha)
  intro j hj
  apply M.columnGrowth_mono hX
    (H (d-j) (by omega) _ (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j hj)) <;> omega

end UnitaryStructure
theorem vacuum_columnGrowth (X : EnergyBand → ℕ → ℝ) : M.ColumnGrowth X A.vacuum 0 0 0 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro τ N v hv
  simp only [physicalMode, Nat.cast_zero, add_zero, M.vacuum_mode, pow_zero, one_mul, mul_one]
  have he (m : ℕ) : (m : ℤ) - 1 = -1 ↔ m = 0 := by omega
  simp only [he]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m hm hm0; simp [hm0]
  · simp

theorem vacuum_sharpGrowth (X : EnergyBand → ℕ → ℝ) (hX : ∀ τ N, 1 ≤ X τ N) : M.SharpGrowth X A.vacuum 0 := by
  constructor
  · simpa only [Nat.mul_zero, Nat.zero_sub] using M.vacuum_columnGrowth X
  · apply M.zeroGrowth_mono hX (M.zeroGrowth_of_columnGrowth (by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _) (M.vacuum_columnGrowth X)) <;> norm_num

 
theorem translation_physicalMode (a : V) (d : ℕ) (m : ℤ) :
    M.physicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • M.physicalMode a d m := by
  simp only [physicalMode, Nat.cast_add, Nat.cast_one]
  rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, M.translation_covariance]
  push_cast
  rfl

theorem translation_columnGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d p q : ℕ}
    (H : M.ColumnGrowth X a d p q) :
    M.ColumnGrowth X (A.toVertexAlgebra.translation a) (d+1) (p+2) q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro τ N v hv
  have hcoef (m : ℕ) (hm : m ∈ Finset.range (N + 1)) :
      ‖(-((m : ℂ) + d))‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2 := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by have := Finset.mem_range.mp hm; omega)
    have he : ‖(-((m : ℂ) + d))‖ = (m + d : ℝ) := by
      rw [norm_neg, ← Nat.cast_add, Complex.norm_natCast, Nat.cast_add]
    rw [he, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) N]
  have hXN := zero_le_one.trans (hX τ N)
  calc
    _ = ∑ m ∈ Finset.range (N + 1), ‖(-((m : ℂ) + d))‖^2 * ‖M.physicalMode a d m v‖^2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [M.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow, Int.cast_natCast]
    _ ≤ ∑ m ∈ Finset.range (N + 1), ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ‖M.physicalMode a d m v‖^2 :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right (hcoef m hm) (sq_nonneg _)
    _ = ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2 := by rw [Finset.mul_sum]
    _ ≤ ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * (C * (N + 1 : ℝ)^p * X τ N^q * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left (HC τ N v hv) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem translation_zeroGrowth {X : EnergyBand → ℕ → ℝ} {a : V} {d p q : ℕ}
    (H : M.ZeroGrowth X a d p q) :
    M.ZeroGrowth X (A.toVertexAlgebra.translation a) (d+1) p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d : ℝ)^2 * C, by positivity, ?_⟩
  intro τ N v hv
  rw [M.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow]
  simp only [Int.cast_zero, zero_add, norm_neg, Complex.norm_natCast]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (HC τ N v hv) (sq_nonneg (d : ℝ))

theorem translation_sharpGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (H : M.SharpGrowth X a d) :
    M.SharpGrowth X (A.toVertexAlgebra.translation a) (d+1) := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨M.columnGrowth_zero X _ _ _, M.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact M.columnGrowth_mono hX (M.translation_columnGrowth hX H.1) (by omega) (by omega)
    · exact M.zeroGrowth_mono hX (M.translation_zeroGrowth H.2) (by omega) (by omega)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem normalProduct_degreeGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N)
    {a b : V} {d e u t : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (Ha : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ a d N (C * (N + 1 : ℝ)^(2*d-1) * X τ N^(2*u)) ∧
      Q.AdjointColumnControl τ a d N (C * (N + 1 : ℝ)^(2*d-1) * X τ N^(2*u)))
    (Hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ b e N (C * (N + 1 : ℝ)^(2*e-1) * X τ N^(2*t)) ∧
      Q.AdjointColumnControl τ b e N (C * (N + 1 : ℝ)^(2*e-1) * X τ N^(2*t)))
    (Hsing : ∀ j < d - 1,
      M.ColumnGrowth X (mode A.fields a j b) (d+e-j-1) (2*(d+e)-2) (2*(u+t))) :
    M.SharpDegreeGrowth X (mode A.fields a (-1) b) (d+e) (u+t) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  obtain ⟨R, hR, HR⟩ := M.finite_columnGrowth_uniform hX (Finset.range (d-1))
    (fun j => mode A.fields a j b) (fun j => d+e-j-1) (2*(d+e)-2) (2*(u+t)) (fun j hj => Hsing j (Finset.mem_range.mp hj))
  have hM := sharpCorrectionMass_nonneg d
  have hconst : 0 ≤ 12 * C * D + 4 * sharpCorrectionMass d * R := by positivity
  have hp : (2*d-1)+(2*e-1) = 2*(d+e)-2 := by omega
  have hp' : (2*d-1)+(2*e-1)+1 = 2*(d+e)-1 := by omega
  have hq : 2*u+2*t = 2*(u+t) := by omega
  constructor
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro τ N
    have hXN := zero_le_one.trans (hX τ N)
    apply M.columnControl_mono τ (Q.normalProduct_columnControl τ ha hb hd
      (by positivity) (by positivity) (HC τ N).1 (HC τ N).2 (HD τ N).1 (HD τ N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) τ N))
    have hpow : (N + 1 : ℝ)^(2*(d+e)-2) ≤ (N + 1 : ℝ)^(2*(d+e)-1) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    calc
      _ = 12*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1)+1)*X τ N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X τ N^(2*(u+t)) := by
        simp only [pow_add, pow_one]; ring
      _ ≤ 12*C*D*(N + 1 : ℝ)^(2*(d+e)-1)*X τ N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-1)*X τ N^(2*(u+t)) := by
        rw [hp', hq]
        gcongr
      _ = _ := by ring
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro τ N v hv
    have hXN := zero_le_one.trans (hX τ N)
    apply (Q.normalProduct_zero_sq_le τ ha hb hd hv
      (by positivity) (by positivity) (HC τ N).1 (HC τ N).2 (HD τ N).1 (HD τ N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) τ N)).trans
    have hmax : max 1 (2*(d+e)-2) = 2*(d+e)-2 := by omega
    rw [hmax]
    calc
      _ = (8*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1))*X τ N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X τ N^(2*(u+t))) * ‖v‖^2 := by
        simp only [pow_add]; ring
      _ ≤ (12*C*D*(N + 1 : ℝ)^(2*(d+e)-2)*X τ N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X τ N^(2*(u+t))) * ‖v‖^2 := by
        rw [hp, hq]
        gcongr
        norm_num
      _ = _ := by ring

end UnitaryStructure
def sharpDegreeGrowthSubmodule (X : EnergyBand → ℕ → ℝ) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | M.SharpDegreeGrowth X a d w}
  zero_mem' := ⟨M.columnGrowth_zero X d _ _, M.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨M.columnGrowth_add h.1 k.1, M.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨M.columnGrowth_smul h.1 z, M.zeroGrowth_smul h.2 z⟩

theorem sharpDegreeGrowth_mono {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d w w' : ℕ}
    (H : M.SharpDegreeGrowth X a d w) (hw : w ≤ w') : M.SharpDegreeGrowth X a d w' :=
  ⟨M.columnGrowth_mono hX H.1 le_rfl (by omega), M.zeroGrowth_mono hX H.2 le_rfl (by omega)⟩

theorem translation_sharpDegreeGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d w : ℕ}
    (ha : a ∈ A.grade d) (H : M.SharpDegreeGrowth X a d w) :
    M.SharpDegreeGrowth X (A.toVertexAlgebra.translation a) (d+1) w := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨M.columnGrowth_zero X _ _ _, M.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact M.columnGrowth_mono hX (M.translation_columnGrowth hX H.1) (by omega) le_rfl
    · exact M.zeroGrowth_mono hX (M.translation_zeroGrowth H.2) (by omega) le_rfl

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem adjointPhysicalMode_translation {a : V} {d : ℕ} (ha : a ∈ A.grade d) (m : ℤ) :
    Q.adjointPhysicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • Q.adjointPhysicalMode a d m := by
  have hT : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [← Q.adjointPhysicalMode_inner hT, M.translation_physicalMode, LinearMap.smul_apply,
    inner_smul_left, Q.adjointPhysicalMode_inner ha, LinearMap.smul_apply, inner_smul_right]
  simp

theorem translation_bothColumnGrowth {X : EnergyBand → ℕ → ℝ} (hX : ∀ τ N, 1 ≤ X τ N) {a : V} {d p q : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ a d N (C * (N + 1 : ℝ)^p * X τ N^q) ∧
      Q.AdjointColumnControl τ a d N (C * (N + 1 : ℝ)^p * X τ N^q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ N,
      M.ColumnControl τ (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X τ N^q) ∧
      Q.AdjointColumnControl τ (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X τ N^q) := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro τ N
  have hXN := zero_le_one.trans (hX τ N)
  have hcoef (m : ℕ) (hm : m ∈ Finset.range (N+1)) (ε : ℤ) (hε : |(ε : ℝ)| ≤ 1) :
      ‖-(((ε * m : ℤ) : ℂ) + d)‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2 := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by have := Finset.mem_range.mp hm; omega)
    have hn : ‖-(((ε * m : ℤ) : ℂ) + d)‖ ≤ (d + 1 : ℝ) * (N + 1 : ℝ) := by
      rw [norm_neg]
      calc
        _ ≤ ‖(((ε * m : ℤ) : ℂ))‖ + ‖(d : ℂ)‖ := norm_add_le _ _
        _ = |(ε : ℝ)| * m + d := by simp only [Int.cast_mul, Int.cast_natCast,
          norm_mul, Complex.norm_intCast, Complex.norm_natCast]
        _ ≤ (m : ℝ) + d := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
        _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) N]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have step (F G : ℕ → Module.End ℂ W)
      (hf : ∀ m, ∃ z : ℂ, G m = z • F m ∧
        (m ∈ Finset.range (N+1) → ‖z‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2))
      (hF : ∀ v ∈ M.energyCutoff τ N, (∑ m ∈ Finset.range (N+1), ‖F m v‖^2) ≤ C*(N+1 : ℝ)^p*X τ N^q*‖v‖^2) :
      ∀ v ∈ M.energyCutoff τ N, (∑ m ∈ Finset.range (N+1), ‖G m v‖^2) ≤
        ((d+1 : ℝ)^2*C)*(N+1 : ℝ)^(p+2)*X τ N^q*‖v‖^2 := by
    intro v hv
    calc
      _ ≤ ∑ m ∈ Finset.range (N+1), ((d+1 : ℝ)^2*(N+1 : ℝ)^2)*‖F m v‖^2 := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨z, hz, hzn⟩ := hf m
        rw [hz, LinearMap.smul_apply, norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right (hzn hm) (sq_nonneg _)
      _ = ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * ∑ m ∈ Finset.range (N+1), ‖F m v‖^2 := by rw [Finset.mul_sum]
      _ ≤ ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * (C*(N+1 : ℝ)^p*X τ N^q*‖v‖^2) :=
        mul_le_mul_of_nonneg_left (hF v hv) (by positivity)
      _ = _ := by rw [pow_add]; ring
  constructor
  · apply step (fun m => M.physicalMode a d m) _ _ (HC τ N).1
    intro m
    refine ⟨-((m : ℂ)+d), ?_, ?_⟩
    · simpa only [Int.cast_natCast] using M.translation_physicalMode a d m
    · intro hm
      simpa using hcoef m hm 1 (by norm_num)
  · apply step (fun m => Q.adjointPhysicalMode a d (-(m : ℤ))) _ _ (HC τ N).2
    intro m
    refine ⟨-((-(m : ℤ) : ℤ) + d : ℂ), ?_, ?_⟩
    · simpa only [Int.cast_add, Int.cast_natCast] using Q.adjointPhysicalMode_translation ha (-(m : ℤ))
    · intro hm
      simpa using hcoef m hm (-1) (by norm_num)

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
