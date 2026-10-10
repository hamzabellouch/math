import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.ColumnControl

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
def adjointMass (d : ℕ) : ℝ :=
  (d + 1 : ℝ) * ∑ j ∈ Finset.range (d + 1), ‖(j.factorial : ℂ)⁻¹‖^2

theorem adjointMass_nonneg (d : ℕ) : 0 ≤ adjointMass d := by unfold adjointMass; positivity

theorem adjointColumnControl_of_columns {a : V} {d N : ℕ} {R : ℝ}
    (H : ∀ j ≤ d, A.ColumnControl ((A.virasoroMode 1^j) (U.pct a)) (d-j) N R) :
    U.AdjointColumnControl a d N (adjointMass d * R) := by
  intro v hv
  let T := fun j m : ℕ => (j.factorial : ℂ)⁻¹ •
    A.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) m v
  have hT (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖T j m‖^2) ≤ ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2 := by
    have H' := H j (by have := Finset.mem_range.mp hj; omega) v hv
    simpa only [T, norm_smul, mul_pow, ← Finset.mul_sum, mul_assoc] using
      mul_le_mul_of_nonneg_left H' (sq_nonneg ‖(j.factorial : ℂ)⁻¹‖)
  have h := SharpColumns.sum_columns_sq_le (Finset.range (d + 1)) (Finset.range (N + 1))
    T (fun j => ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2) hT
  simpa only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    neg_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    adjointMass, Finset.card_range, Nat.cast_add, Nat.cast_one, Finset.sum_mul, mul_assoc, T] using h

 

theorem bothColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q)
    (H : ∀ j ≤ d, A.ColumnGrowth X ((A.virasoroMode 1^j) (U.pct a)) (d-j) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨R, hR, HR⟩ := A.finite_columnGrowth_uniform hX (Finset.range (d + 1))
    (fun j => (A.virasoroMode 1^j) (U.pct a)) (fun j => d-j) p q
    (fun j hj => H j (by have := Finset.mem_range.mp hj; omega))
  refine ⟨C + adjointMass d * R, add_nonneg hC (mul_nonneg (adjointMass_nonneg d) hR), ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX N)
  have hM := adjointMass_nonneg d
  constructor
  · apply A.columnControl_mono (HC N)
    gcongr
    exact le_add_of_nonneg_right (mul_nonneg hM hR)
  · intro v hv
    have H' := U.adjointColumnControl_of_columns
      (fun j hj => HR j (Finset.mem_range.mpr (by omega)) N) v hv
    apply H'.trans
    calc
      _ = (adjointMass d * R) * (N + 1 : ℝ)^p * X N^q * ‖v‖^2 := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left hC

theorem bothSharpColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∀ e ≤ d, ∀ b ∈ A.grade e, A.ColumnGrowth X b e (2*e-1) (2*e)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*d)) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*d)) := by
  apply U.bothColumnGrowth hX (H d le_rfl a ha)
  intro j hj
  apply A.columnGrowth_mono hX
    (H (d-j) (by omega) _ (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j hj)) <;> omega

end UnitaryStructure

 

theorem vacuum_columnGrowth (X : ℕ → ℝ) : A.ColumnGrowth X A.vacuum 0 0 0 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro N v hv
  simp only [physicalMode, Nat.cast_zero, add_zero, A.vacuum_mode, pow_zero, one_mul, mul_one]
  have he (m : ℕ) : (m : ℤ) - 1 = -1 ↔ m = 0 := by omega
  simp only [he]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m hm hm0; simp [hm0]
  · simp

theorem vacuum_sharpGrowth (X : ℕ → ℝ) (hX : ∀ N, 1 ≤ X N) : A.SharpGrowth X A.vacuum 0 := by
  constructor
  · simpa only [Nat.mul_zero, Nat.zero_sub] using A.vacuum_columnGrowth X
  · apply A.zeroGrowth_mono hX (A.zeroGrowth_of_columnGrowth (by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _) (A.vacuum_columnGrowth X)) <;> norm_num

 
theorem translation_physicalMode (a : V) (d : ℕ) (m : ℤ) :
    A.physicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • A.physicalMode a d m := by
  simp only [physicalMode, Nat.cast_add, Nat.cast_one]
  rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, A.translation_covariance]
  push_cast
  rfl

theorem translation_columnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (H : A.ColumnGrowth X a d p q) :
    A.ColumnGrowth X (A.toVertexAlgebra.translation a) (d+1) (p+2) q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro N v hv
  have hcoef (m : ℕ) (hm : m ∈ Finset.range (N + 1)) :
      ‖(-((m : ℂ) + d))‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2 := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by have := Finset.mem_range.mp hm; omega)
    have he : ‖(-((m : ℂ) + d))‖ = (m + d : ℝ) := by
      rw [norm_neg, ← Nat.cast_add, Complex.norm_natCast, Nat.cast_add]
    rw [he, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) N]
  have hXN := zero_le_one.trans (hX N)
  calc
    _ = ∑ m ∈ Finset.range (N + 1), ‖(-((m : ℂ) + d))‖^2 * ‖A.physicalMode a d m v‖^2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [A.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow, Int.cast_natCast]
    _ ≤ ∑ m ∈ Finset.range (N + 1), ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ‖A.physicalMode a d m v‖^2 :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right (hcoef m hm) (sq_nonneg _)
    _ = ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by rw [Finset.mul_sum]
    _ ≤ ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * (C * (N + 1 : ℝ)^p * X N^q * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left (HC N v hv) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem translation_zeroGrowth {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (H : A.ZeroGrowth X a d p q) :
    A.ZeroGrowth X (A.toVertexAlgebra.translation a) (d+1) p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d : ℝ)^2 * C, by positivity, ?_⟩
  intro N v hv
  rw [A.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow]
  simp only [Int.cast_zero, zero_add, norm_neg, Complex.norm_natCast]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg (d : ℝ))

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem translation_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (H : A.SharpGrowth X a d) :
    A.SharpGrowth X (A.toVertexAlgebra.translation a) (d+1) := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact A.columnGrowth_mono hX (A.translation_columnGrowth hX H.1) (by omega) (by omega)
    · exact A.zeroGrowth_mono hX (A.translation_zeroGrowth H.2) (by omega) (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalProduct_degreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a b : V} {d e u t : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (Ha : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*u)) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*u)))
    (Hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl b e N (C * (N + 1 : ℝ)^(2*e-1) * X N^(2*t)) ∧
      U.AdjointColumnControl b e N (C * (N + 1 : ℝ)^(2*e-1) * X N^(2*t)))
    (Hsing : ∀ j < d - 1,
      A.ColumnGrowth X (mode A.fields a j b) (d+e-j-1) (2*(d+e)-2) (2*(u+t))) :
    A.SharpDegreeGrowth X (mode A.fields a (-1) b) (d+e) (u+t) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  obtain ⟨R, hR, HR⟩ := A.finite_columnGrowth_uniform hX (Finset.range (d-1))
    (fun j => mode A.fields a j b) (fun j => d+e-j-1) (2*(d+e)-2) (2*(u+t)) (fun j hj => Hsing j (Finset.mem_range.mp hj))
  have hM := sharpCorrectionMass_nonneg d
  have hconst : 0 ≤ 12 * C * D + 4 * sharpCorrectionMass d * R := by positivity
  have hp : (2*d-1)+(2*e-1) = 2*(d+e)-2 := by omega
  have hp' : (2*d-1)+(2*e-1)+1 = 2*(d+e)-1 := by omega
  have hq : 2*u+2*t = 2*(u+t) := by omega
  constructor
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro N
    have hXN := zero_le_one.trans (hX N)
    apply A.columnControl_mono (U.normalProduct_columnControl ha hb hd
      (by positivity) (by positivity) (HC N).1 (HC N).2 (HD N).1 (HD N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) N))
    have hpow : (N + 1 : ℝ)^(2*(d+e)-2) ≤ (N + 1 : ℝ)^(2*(d+e)-1) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    calc
      _ = 12*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1)+1)*X N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t)) := by
        simp only [pow_add, pow_one]; ring
      _ ≤ 12*C*D*(N + 1 : ℝ)^(2*(d+e)-1)*X N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-1)*X N^(2*(u+t)) := by
        rw [hp', hq]
        gcongr
      _ = _ := by ring
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro N v hv
    have hXN := zero_le_one.trans (hX N)
    apply (U.normalProduct_zero_sq_le ha hb hd hv
      (by positivity) (by positivity) (HC N).1 (HC N).2 (HD N).1 (HD N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) N)).trans
    have hmax : max 1 (2*(d+e)-2) = 2*(d+e)-2 := by omega
    rw [hmax]
    calc
      _ = (8*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1))*X N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t))) * ‖v‖^2 := by
        simp only [pow_add]; ring
      _ ≤ (12*C*D*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t))) * ‖v‖^2 := by
        rw [hp, hq]
        gcongr
        norm_num
      _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

def sharpDegreeGrowthSubmodule (X : ℕ → ℝ) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | A.SharpDegreeGrowth X a d w}
  zero_mem' := ⟨A.columnGrowth_zero X d _ _, A.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨A.columnGrowth_add h.1 k.1, A.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨A.columnGrowth_smul h.1 z, A.zeroGrowth_smul h.2 z⟩

theorem sharpDegreeGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d w w' : ℕ}
    (H : A.SharpDegreeGrowth X a d w) (hw : w ≤ w') : A.SharpDegreeGrowth X a d w' :=
  ⟨A.columnGrowth_mono hX H.1 le_rfl (by omega), A.zeroGrowth_mono hX H.2 le_rfl (by omega)⟩

theorem translation_sharpDegreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d w : ℕ}
    (ha : a ∈ A.grade d) (H : A.SharpDegreeGrowth X a d w) :
    A.SharpDegreeGrowth X (A.toVertexAlgebra.translation a) (d+1) w := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact A.columnGrowth_mono hX (A.translation_columnGrowth hX H.1) (by omega) le_rfl
    · exact A.zeroGrowth_mono hX (A.translation_zeroGrowth H.2) (by omega) le_rfl

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem adjointPhysicalMode_translation {a : V} {d : ℕ} (ha : a ∈ A.grade d) (m : ℤ) :
    U.adjointPhysicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • U.adjointPhysicalMode a d m := by
  have hT : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [← U.adjointPhysicalMode_inner hT, A.translation_physicalMode, LinearMap.smul_apply,
    inner_smul_left, U.adjointPhysicalMode_inner ha, LinearMap.smul_apply, inner_smul_right]
  simp

theorem translation_bothColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X N^q) ∧
      U.AdjointColumnControl (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X N^q) := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX N)
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
  have step (F G : ℕ → Module.End ℂ V)
      (hf : ∀ m, ∃ z : ℂ, G m = z • F m ∧
        (m ∈ Finset.range (N+1) → ‖z‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2))
      (hF : ∀ v ∈ A.energyCutoff N, (∑ m ∈ Finset.range (N+1), ‖F m v‖^2) ≤ C*(N+1 : ℝ)^p*X N^q*‖v‖^2) :
      ∀ v ∈ A.energyCutoff N, (∑ m ∈ Finset.range (N+1), ‖G m v‖^2) ≤
        ((d+1 : ℝ)^2*C)*(N+1 : ℝ)^(p+2)*X N^q*‖v‖^2 := by
    intro v hv
    calc
      _ ≤ ∑ m ∈ Finset.range (N+1), ((d+1 : ℝ)^2*(N+1 : ℝ)^2)*‖F m v‖^2 := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨z, hz, hzn⟩ := hf m
        rw [hz, LinearMap.smul_apply, norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right (hzn hm) (sq_nonneg _)
      _ = ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * ∑ m ∈ Finset.range (N+1), ‖F m v‖^2 := by rw [Finset.mul_sum]
      _ ≤ ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * (C*(N+1 : ℝ)^p*X N^q*‖v‖^2) :=
        mul_le_mul_of_nonneg_left (hF v hv) (by positivity)
      _ = _ := by rw [pow_add]; ring
  constructor
  · apply step (fun m => A.physicalMode a d m) _ _ (HC N).1
    intro m
    refine ⟨-((m : ℂ)+d), ?_, ?_⟩
    · simpa only [Int.cast_natCast] using A.translation_physicalMode a d m
    · intro hm
      simpa using hcoef m hm 1 (by norm_num)
  · apply step (fun m => U.adjointPhysicalMode a d (-(m : ℤ))) _ _ (HC N).2
    intro m
    refine ⟨-((-(m : ℤ) : ℤ) + d : ℂ), ?_, ?_⟩
    · simpa only [Int.cast_add, Int.cast_natCast] using U.adjointPhysicalMode_translation ha (-(m : ℤ))
    · intro hm
      simpa using hcoef m hm (-1) (by norm_num)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U

 

theorem homogeneousC2_le_sharpDegreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, A.SharpGrowth X a d) :
    A.homogeneousC2 w ≤ A.sharpDegreeGrowthSubmodule X w (w-1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change A.SharpDegreeGrowth X (mode A.fields a (-2) b) w (w-1)
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := A.translation_sharpDegreeGrowth hX ha (hprev d (by omega) a ha)
    rw [hweight']
    change A.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) (d+1-1)
    simpa only [Nat.add_sub_cancel] using
      (show A.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) d from
        ⟨A.columnGrowth_smul H.1 z, A.zeroGrowth_smul H.2 z⟩)
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [mode_smul, LinearMap.smul_apply, A.vacuum_mode]
    norm_num
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  have hTa : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  have Ha := U.bothSharpColumnGrowth hX ha
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HT := U.translation_bothColumnGrowth hX ha Ha
  have hpexp : (2*d-1)+2 = 2*(d+1)-1 := by omega
  rw [hpexp] at HT
  have HB := U.bothSharpColumnGrowth hX hb
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HS : ∀ j < (d+1)-1,
      A.ColumnGrowth X (mode A.fields (A.toVertexAlgebra.translation a) j b)
        (d+1+e-j-1) (2*(d+1+e)-2) (2*(d+e)) := by
    intro j hj
    have hgrade := A.mode_mem_grade hTa hb (j : ℤ)
      (k := d+1+e-j-1) (by omega)
    exact A.columnGrowth_mono hX (hprev _ (by omega) _ hgrade).1 (by omega) (by omega)
  have H := U.normalProduct_degreeGrowth hX hTa hb (by omega) (by omega) HT HB HS
  have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b = mode A.fields a (-2) b := by
    rw [A.translation_covariance]
    norm_num
  rw [heq] at H
  convert H using 1 <;> omega

 

theorem grade_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      A.SharpGrowth X a d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, A.SharpGrowth X a d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨A.columnGrowth_smul (A.vacuum_sharpGrowth X hX).1 z,
        A.zeroGrowth_smul (A.vacuum_sharpGrowth X hX).2 z⟩
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      have H := A.translation_sharpGrowth hX hb (ih e (by omega) b hb)
      have Q := hsmall _ (by omega) hdD q hq hqq
      exact ⟨A.columnGrowth_add Q.1 H.1, A.zeroGrowth_add Q.2 H.2⟩
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact A.sharpDegreeGrowth_mono hX
        (U.homogeneousC2_le_sharpDegreeGrowth hX d ih hc) (by omega)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 
def zeroModeOnCutoff (a : V) (d N : ℕ) : A.energyCutoff N →L[ℂ] V :=
  LinearMap.toContinuousLinearMap ((A.physicalMode a d 0).comp (A.energyCutoff N).subtype)

def zeroModeCutoffNorm (a : V) (d N : ℕ) : ℝ := ‖A.zeroModeOnCutoff a d N‖

theorem zeroMode_norm_le (a : V) (d : ℕ) {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) :
    ‖A.physicalMode a d 0 v‖ ≤ A.zeroModeCutoffNorm a d N * ‖v‖ :=
  (A.zeroModeOnCutoff a d N).le_opNorm ⟨v, hv⟩

theorem zeroModeCutoffNorm_mono (a : V) (d : ℕ) : Monotone (A.zeroModeCutoffNorm a d) := by
  intro N M hNM
  change ‖A.zeroModeOnCutoff a d N‖ ≤ ‖A.zeroModeOnCutoff a d M‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (A.zeroModeOnCutoff a d M))
  intro v
  exact A.zeroMode_norm_le a d (A.energyCutoff_mono hNM v.property)

 

def sharpColumnQuantity (a : V) (d N : ℕ) : ℝ :=
  A.positiveColumnNorm a d N ^ 2 / (N+1 : ℝ)^(2*d-1)

def sharpZeroQuantity (a : V) (d N : ℕ) : ℝ :=
  A.zeroModeCutoffNorm a d N ^ 2 / (N+1 : ℝ)^(max 1 (2*d-2))

def rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹)

 

def sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (A.rawSharpMajorant D S)

theorem sharpColumnQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ A.sharpColumnQuantity a d N := by
  unfold sharpColumnQuantity
  positivity

theorem sharpZeroQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ A.sharpZeroQuantity a d N := by
  unfold sharpZeroQuantity
  positivity

theorem one_le_rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.rawSharpMajorant D S N := by
  unfold rawSharpMajorant
  have H : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro a _
    exact add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
  linarith

theorem rawSharpMajorant_le (D : ℕ) (S : ℕ → Finset V) {N M : ℕ} (hNM : N ≤ M) :
    A.rawSharpMajorant D S N ≤ A.sharpMajorant D S M := by
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem one_le_sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.sharpMajorant D S N :=
  (A.one_le_rawSharpMajorant D S N).trans (A.rawSharpMajorant_le D S le_rfl)

theorem sharpMajorant_mono (D : ℕ) (S : ℕ → Finset V) : Monotone (A.sharpMajorant D S) := by
  intro N M hNM
  apply Finset.sup'_le
  intro k hk
  exact A.rawSharpMajorant_le D S (by have := Finset.mem_range.mp hk; omega)

theorem root_sharpQuantity_le (D : ℕ) (S : ℕ → Finset V) {N d : ℕ} {a : V}
    (hd : d ≤ D) (ha : a ∈ S d) :
    (A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ A.sharpMajorant D S N ∧
    (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ A.sharpMajorant D S N := by
  let F (e : ℕ) (b : V) := (A.sharpColumnQuantity b e N)^((2*e : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity b e N)^((2*e : ℕ) : ℝ)⁻¹
  have hF (e : ℕ) (b : V) : 0 ≤ F e b :=
    add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg b e N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg b e N) _)
  have H₁ := Finset.single_le_sum (fun b _ => hF d b) ha
  have H₂ := Finset.single_le_sum (s := Finset.range (D+1)) (a := d) (f := fun e => ∑ b ∈ S e, F e b)
    (fun e _ => Finset.sum_nonneg (fun b _ => hF e b)) (Finset.mem_range.mpr (by omega))
  have H₃ : F d a ≤ A.sharpMajorant D S N := by
    apply (H₁.trans H₂).trans
    exact (le_add_of_nonneg_left zero_le_one).trans (A.rawSharpMajorant_le D S le_rfl)
  constructor
  · exact (le_add_of_nonneg_right (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)).trans H₃
  · exact (le_add_of_nonneg_left (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)).trans H₃
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
