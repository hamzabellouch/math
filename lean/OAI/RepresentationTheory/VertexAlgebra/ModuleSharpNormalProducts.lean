import OAI.RepresentationTheory.VertexAlgebra.ModuleColumnOperators

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
variable (τ : EnergyBand)
def ColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ M.energyCutoff τ N,
    (∑ m ∈ Finset.range (N + 1), ‖M.physicalMode a d m v‖^2) ≤ K * ‖v‖^2

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem columnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : M.ColumnControl τ a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : W} (hv : v ∈ M.energyCutoff τ N) :
    (∑ i ∈ s, ‖M.physicalMode a d (f i) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf (fun m => ‖M.physicalMode a d m v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [Q.physicalMode_zero_above_cutoff τ ha hv m (by exact_mod_cast hm)]
  simp

def AdjointColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ M.energyCutoff τ N,
    (∑ m ∈ Finset.range (N + 1), ‖Q.adjointPhysicalMode a d (-(m : ℤ)) v‖^2) ≤ K * ‖v‖^2

theorem adjointColumnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : Q.AdjointColumnControl τ a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : W} (hv : v ∈ M.energyCutoff τ N) :
    (∑ i ∈ s, ‖Q.adjointPhysicalMode a d (-(f i : ℤ)) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf
    (fun m => ‖Q.adjointPhysicalMode a d (-(m : ℤ)) v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [Q.adjointPhysicalMode_zero_above_cutoff τ ha hv m (by exact_mod_cast hm)]
  simp

end UnitaryStructure
def normalLeft (a b : V) (v : W) (d e N m : ℕ) : W :=
  ∑ j ∈ Finset.range (N + 1), M.physicalMode a d (-1 - j)
    (M.physicalMode b e (m + 1 + j) v)

def normalRightHigh (a b : V) (v : W) (d e N m : ℕ) : W :=
  ∑ j ∈ Finset.range (N + 1) with m ≤ j, M.physicalMode b e ((m : ℤ) - j)
    (M.physicalMode a d j v)

def normalRightLow (a b : V) (v : W) (d e N m : ℕ) : W :=
  ∑ j ∈ Finset.range (N + 1) with j < m, M.physicalMode b e ((m : ℤ) - j)
    (M.physicalMode a d j v)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem normalLeft_mem_cutoff {a b : V} {v : W} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N) :
    M.normalLeft a b v d e N m ∈ M.energyCutoff τ N := by
  apply Submodule.sum_mem
  intro j _
  by_cases hj : N < m + 1 + j
  · rw [Q.physicalMode_zero_above_cutoff τ hb hv (m + 1 + j) (by exact_mod_cast hj), map_zero]
    exact Submodule.zero_mem _
  · have hinner := Q.physicalMode_mem_cutoff τ hb hv (m + 1 + j) (K := N - (m + 1 + j)) (by omega)
    exact Q.physicalMode_mem_cutoff τ ha hinner (-1 - j) (by omega)

theorem normalRightHigh_mem_cutoff {a b : V} {v : W} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N) :
    M.normalRightHigh a b v d e N m ∈ M.energyCutoff τ N := by
  apply Submodule.sum_mem
  intro j hj
  have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hinner := Q.physicalMode_mem_cutoff τ ha hv j (K := N - j) (by omega)
  exact Q.physicalMode_mem_cutoff τ hb hinner ((m : ℤ) - j) (by omega)

theorem normalRightLow_mem_cutoff {a b : V} {v : W} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N) :
    M.normalRightLow a b v d e N m ∈ M.energyCutoff τ N := by
  apply Submodule.sum_mem
  intro j hj
  have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hinner := Q.physicalMode_mem_cutoff τ ha hv j (K := N - j) (by omega)
  exact Q.physicalMode_mem_cutoff τ hb hinner ((m : ℤ) - j) (by omega)

theorem normalLeft_sq_le {a b : V} {v : W} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N)
    (hK : 0 ≤ K) (Ha : Q.AdjointColumnControl τ a d N K) (Hb : M.ColumnControl τ b e N L) :
    ‖M.normalLeft a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  have H := SharpColumns.row_sq_le (Finset.range (N + 1))
    (fun j => M.physicalMode a d (-1 - j))
    (fun j => Q.adjointPhysicalMode a d (-1 - j))
    (M.energyCutoff τ N) K hK (fun j _ x y => Q.adjointPhysicalMode_inner ha _ x y)
    (fun w hw => by
      have HH := Q.adjointColumnControl_subset τ ha Ha (Finset.range (N + 1))
        (fun j => j + 1) (by intro i _ j _ he; dsimp only at he; omega) hw
      simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev, sub_eq_add_neg] using HH)
    (fun j => M.physicalMode b e (m + 1 + j) v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalLeft] using Q.normalLeft_mem_cutoff τ ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := Q.columnControl_subset τ hb Hb (Finset.range (N + 1))
    (fun j => m + 1 + j) (by intro i _ j _ he; dsimp only at he; omega) hv
  push_cast at HH
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HH hK

theorem normalRightHigh_sq_le {a b : V} {v : W} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N)
    (hL : 0 ≤ L) (Ha : M.ColumnControl τ a d N K) (Hb : Q.AdjointColumnControl τ b e N L) :
    ‖M.normalRightHigh a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  let s := (Finset.range (N + 1)).filter (fun j => m ≤ j)
  have H := SharpColumns.row_sq_le s
    (fun j => M.physicalMode b e ((m : ℤ) - j))
    (fun j => Q.adjointPhysicalMode b e ((m : ℤ) - j))
    (M.energyCutoff τ N) L hL (fun j _ x y => Q.adjointPhysicalMode_inner hb _ x y)
    (fun w hw => by
      have HH := Q.adjointColumnControl_subset τ hb Hb s
        (fun j => j - m) (by
          intro i hi j hj he
          dsimp only at he
          have hi := (Finset.mem_filter.mp hi).2
          have hj := (Finset.mem_filter.mp hj).2
          omega) hw
      calc
        _ = ∑ j ∈ s, ‖Q.adjointPhysicalMode b e (-((j - m : ℕ) : ℤ)) w‖^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj := (Finset.mem_filter.mp hj).2
          rw [show (m : ℤ) - j = -((j - m : ℕ) : ℤ) by omega]
        _ ≤ _ := HH)
    (fun j => M.physicalMode a d j v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalRightHigh, s] using Q.normalRightHigh_mem_cutoff τ ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := Q.columnControl_subset τ ha Ha s id (by intro i _ j _ h; exact h) hv
  calc
    _ ≤ L * (K * ‖v‖^2) := mul_le_mul_of_nonneg_left HH hL
    _ = _ := by ring

theorem normalRightLow_column_sq_le {a b : V} {v : W} {d e N : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ M.energyCutoff τ N)
    (hL : 0 ≤ L) (Ha : M.ColumnControl τ a d N K) (Hb : M.ColumnControl τ b e N L) :
    (∑ m ∈ Finset.range (N + 1), ‖M.normalRightLow a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
  classical
  have H := SharpColumns.triangular_column_sq_le (Finset.range (N + 1)) (Finset.range (N + 1))
    (fun j => M.physicalMode a d j v) (fun m j => M.physicalMode b e ((m : ℤ) - j))
    (fun m j => j < m) (fun _ _ => 1) 1 L
    (by intro m _ j _ _; simp)
    (by
      intro j hj
      have hmem := Q.physicalMode_mem_cutoff τ ha hv j (K := N) (by omega)
      have HH := Q.columnControl_subset τ hb Hb ((Finset.range (N + 1)).filter (fun m => j < m))
        (fun m => m - j) (by
          intro r hr s hs he
          dsimp only at he
          have hr := (Finset.mem_filter.mp hr).2
          have hs := (Finset.mem_filter.mp hs).2
          omega) hmem
      calc
        _ = ∑ m ∈ Finset.range (N + 1) with j < m,
            ‖M.physicalMode b e ((m - j : ℕ) : ℤ) (M.physicalMode a d j v)‖^2 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_filter.mp hm).2)]
        _ ≤ _ := HH)
  simp only [one_smul, one_pow, mul_one, Finset.card_range, Nat.cast_add, Nat.cast_one] at H
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left (Ha v hv)
    (mul_nonneg (by positivity : 0 ≤ (N + 1 : ℝ)) hL)
  simpa only [normalRightLow, mul_assoc, mul_comm K L, mul_left_comm L K] using HH

 

theorem normal_product_cutoff_split {a b : V} {v : W} {d e N : ℕ}
    (hb : b ∈ A.grade e) (ha : a ∈ A.grade d) (hv : v ∈ M.energyCutoff τ N)
    (hd : 1 ≤ d) (m : ℕ) :
    M.physicalMode (mode A.fields a (-1) b) (d + e) m v =
      M.normalLeft a b v d e N m + M.normalRightHigh a b v d e N m +
      M.normalRightLow a b v d e N m -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode M.fields (mode A.fields a j b)
          (m + d + e - 2 - j) v := by
  classical
  rw [M.physical_normal_product_resplit a b v d e hd m]
  have hL : Function.support (fun j : ℕ => M.physicalMode a d (-1 - j)
      (M.physicalMode b e (m + 1 + j) v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change M.physicalMode a d (-1 - j) (M.physicalMode b e (m + 1 + j) v) = 0
    rw [Q.physicalMode_zero_above_cutoff τ hb hv (m + 1 + j) (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => M.physicalMode b e ((m : ℤ) - j)
      (M.physicalMode a d j v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change M.physicalMode b e ((m : ℤ) - j) (M.physicalMode a d j v) = 0
    rw [Q.physicalMode_zero_above_cutoff τ ha hv j (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
    (fun j => m ≤ j) (fun j => M.physicalMode b e ((m : ℤ) - j) (M.physicalMode a d j v))
  simp only [not_le] at hs
  dsimp only [normalLeft, normalRightHigh, normalRightLow]
  rw [← hs]
  simp only [add_assoc]

end UnitaryStructure
theorem singular_correction_column_sq_le {a b : V} {v : W} {d e N : ℕ} {R : ℝ}
    (hd : 1 ≤ d) (Hsing : ∀ j < d - 1,
      M.ColumnControl τ (mode A.fields a j b) (d + e - j - 1) N R)
    (hv : v ∈ M.energyCutoff τ N) :
    (∑ m ∈ Finset.range (N + 1), ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℂ) • mode M.fields (mode A.fields a j b) (m + d + e - 2 - j) v‖^2) ≤
      sharpCorrectionMass d * R * ‖v‖^2 := by
  classical
  let T := fun (i j m : ℕ) => (i.choose j : ℂ) •
    mode M.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hinner (i : ℕ) (hi : i ∈ Finset.range (d - 1)) (j : ℕ)
      (hj : j ∈ Finset.range (i + 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖T i j m‖^2) ≤ (i.choose j : ℝ)^2 * R * ‖v‖^2 := by
    have hjd : j < d - 1 := by have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega
    have he : ∀ m : ℕ, (m : ℤ) + d + e - 2 - j = m + (d + e - j - 1 : ℕ) - 1 := by
      intro m
      omega
    simp only [T, norm_smul, Complex.norm_natCast, mul_pow, he,
      ← Finset.mul_sum]
    simpa only [mul_assoc, physicalMode] using mul_le_mul_of_nonneg_left (Hsing j hjd v hv) (sq_nonneg (i.choose j : ℝ))
  have hi (i : ℕ) (hi : i ∈ Finset.range (d - 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖∑ j ∈ Finset.range (i + 1), T i j m‖^2) ≤
        (i + 1 : ℝ) * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2 * R * ‖v‖^2 := by
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
      SharpColumns.sum_columns_sq_le (Finset.range (i + 1)) (Finset.range (N + 1))
        (T i) (fun j => (i.choose j : ℝ)^2 * R * ‖v‖^2) (hinner i hi)
  have H := SharpColumns.sum_columns_sq_le (Finset.range (d - 1)) (Finset.range (N + 1))
    (fun i m => ∑ j ∈ Finset.range (i + 1), T i j m)
    (fun i => (i + 1 : ℝ) * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2 * R * ‖v‖^2) hi
  simpa only [Finset.card_range, sharpCorrectionMass, Finset.sum_mul, mul_assoc, T] using H

theorem columnControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : M.ColumnControl τ a d N K) (hKL : K ≤ L) : M.ColumnControl τ a d N L := by
  intro v hv
  exact (H v hv).trans (mul_le_mul_of_nonneg_right hKL (sq_nonneg _))

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem columnControl_mode_sq_le {a : V} {v : W} {d N m : ℕ} {K : ℝ}
    (ha : a ∈ A.grade d) (H : M.ColumnControl τ a d N K) (hv : v ∈ M.energyCutoff τ N) :
    ‖M.physicalMode a d m v‖^2 ≤ K * ‖v‖^2 := by
  simpa using Q.columnControl_subset τ ha H {m} id (by intro i _ j _ h; exact h) hv

theorem normalProduct_columnControl {a b : V} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : M.ColumnControl τ a d N K) (Ha' : Q.AdjointColumnControl τ a d N K)
    (Hb : M.ColumnControl τ b e N L) (Hb' : Q.AdjointColumnControl τ b e N L)
    (Hsing : ∀ j < d - 1,
      M.ColumnControl τ (mode A.fields a j b) (d + e - j - 1) N R) :
    M.ColumnControl τ (mode A.fields a (-1) b) (d + e) N
      (12 * (N + 1 : ℝ) * K * L + 4 * sharpCorrectionMass d * R) := by
  intro v hv
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode M.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft : (∑ m ∈ Finset.range (N + 1), ‖M.normalLeft a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => Q.normalLeft_sq_le τ ha hb hv hK Ha' Hb
      _ = _ := by simp [mul_assoc]
  have hhigh : (∑ m ∈ Finset.range (N + 1), ‖M.normalRightHigh a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => Q.normalRightHigh_sq_le τ ha hb hv hL Ha Hb'
      _ = _ := by simp [mul_assoc]
  have hlow := Q.normalRightLow_column_sq_le τ ha hb hv hL Ha Hb
  have hsing := M.singular_correction_column_sq_le τ hd Hsing hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 4 * (‖M.normalLeft a b v d e N m‖^2 +
      ‖M.normalRightHigh a b v d e N m‖^2 + ‖M.normalRightLow a b v d e N m‖^2 + ‖T m‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      rw [Q.normal_product_cutoff_split τ hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ = 4 * ((∑ m ∈ Finset.range (N + 1), ‖M.normalLeft a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖M.normalRightHigh a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖M.normalRightLow a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖T m‖^2)) := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]
    _ ≤ _ := by dsimp only [T] at *; nlinarith

theorem normalProduct_zero_sq_le {a b : V} {v : W} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hv : v ∈ M.energyCutoff τ N) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : M.ColumnControl τ a d N K) (Ha' : Q.AdjointColumnControl τ a d N K)
    (Hb : M.ColumnControl τ b e N L) (Hb' : Q.AdjointColumnControl τ b e N L)
    (Hsing : ∀ j < d - 1,
      M.ColumnControl τ (mode A.fields a j b) (d + e - j - 1) N R) :
    ‖M.physicalMode (mode A.fields a (-1) b) (d + e) 0 v‖^2 ≤
      (8 * K * L + 4 * sharpCorrectionMass d * R) * ‖v‖^2 := by
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode M.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft := Q.normalLeft_sq_le τ (m := 0) ha hb hv hK Ha' Hb
  have hhigh := Q.normalRightHigh_sq_le τ (m := 0) ha hb hv hL Ha Hb'
  have hlow : M.normalRightLow a b v d e N 0 = 0 := by simp [normalRightLow]
  have hsing : ‖T 0‖^2 ≤ sharpCorrectionMass d * R * ‖v‖^2 := by
    apply (Finset.single_le_sum (f := fun m => ‖T m‖^2) (fun _ _ => sq_nonneg _) (by simp : 0 ∈ Finset.range (N + 1))).trans
    exact M.singular_correction_column_sq_le τ hd Hsing hv
  calc
    _ ≤ 4 * (‖M.normalLeft a b v d e N 0‖^2 + ‖M.normalRightHigh a b v d e N 0‖^2 +
      ‖M.normalRightLow a b v d e N 0‖^2 + ‖T 0‖^2) := by
      rw [show (0 : ℤ) = (0 : ℕ) by rfl, Q.normal_product_cutoff_split τ hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ ≤ _ := by rw [hlow, norm_zero, zero_pow (by decide : 2 ≠ 0)]; nlinarith

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
