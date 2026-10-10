import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.ConstrainedSquareBound

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
def ColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ A.energyCutoff N,
    (∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) ≤ K * ‖v‖^2

theorem columnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : A.ColumnControl a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ i ∈ s, ‖A.physicalMode a d (f i) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf (fun m => ‖A.physicalMode a d m v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [A.physicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm)]
  simp

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 
def AdjointColumnControl (a : V) (d N : ℕ) (K : ℝ) : Prop :=
  ∀ v ∈ A.energyCutoff N,
    (∑ m ∈ Finset.range (N + 1), ‖U.adjointPhysicalMode a d (-(m : ℤ)) v‖^2) ≤ K * ‖v‖^2

theorem adjointColumnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : U.AdjointColumnControl a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ i ∈ s, ‖U.adjointPhysicalMode a d (-(f i : ℤ)) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf
    (fun m => ‖U.adjointPhysicalMode a d (-(m : ℤ)) v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [U.adjointPhysicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm)]
  simp

end UnitaryStructure

 
def normalLeft (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1), A.physicalMode a d (-1 - j)
    (A.physicalMode b e (m + 1 + j) v)

def normalRightHigh (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1) with m ≤ j, A.physicalMode b e ((m : ℤ) - j)
    (A.physicalMode a d j v)

def normalRightLow (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1) with j < m, A.physicalMode b e ((m : ℤ) - j)
    (A.physicalMode a d j v)

theorem normalLeft_mem_cutoff {a b v : V} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N) :
    A.normalLeft a b v d e N m ∈ A.energyCutoff N := by
  apply Submodule.sum_mem
  intro j _
  by_cases hj : N < m + 1 + j
  · rw [A.physicalMode_zero_above_cutoff hb hv (m + 1 + j) (by exact_mod_cast hj), map_zero]
    exact Submodule.zero_mem _
  · have hinner := A.physicalMode_mem_cutoff hb hv (m + 1 + j) (M := N - (m + 1 + j)) (by omega)
    exact A.physicalMode_mem_cutoff ha hinner (-1 - j) (by omega)

theorem normalRightHigh_mem_cutoff {a b v : V} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N) :
    A.normalRightHigh a b v d e N m ∈ A.energyCutoff N := by
  apply Submodule.sum_mem
  intro j hj
  have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hinner := A.physicalMode_mem_cutoff ha hv j (M := N - j) (by omega)
  exact A.physicalMode_mem_cutoff hb hinner ((m : ℤ) - j) (by omega)

theorem normalRightLow_mem_cutoff {a b v : V} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N) :
    A.normalRightLow a b v d e N m ∈ A.energyCutoff N := by
  apply Submodule.sum_mem
  intro j hj
  have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hinner := A.physicalMode_mem_cutoff ha hv j (M := N - j) (by omega)
  exact A.physicalMode_mem_cutoff hb hinner ((m : ℤ) - j) (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalLeft_sq_le {a b v : V} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hK : 0 ≤ K) (Ha : U.AdjointColumnControl a d N K) (Hb : A.ColumnControl b e N L) :
    ‖A.normalLeft a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  have H := SharpColumns.row_sq_le (Finset.range (N + 1))
    (fun j => A.physicalMode a d (-1 - j))
    (fun j => U.adjointPhysicalMode a d (-1 - j))
    (A.energyCutoff N) K hK (fun j _ x y => U.adjointPhysicalMode_inner ha _ x y)
    (fun w hw => by
      have HH := U.adjointColumnControl_subset ha Ha (Finset.range (N + 1))
        (fun j => j + 1) (by intro i _ j _ he; dsimp only at he; omega) hw
      simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev, sub_eq_add_neg] using HH)
    (fun j => A.physicalMode b e (m + 1 + j) v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalLeft] using A.normalLeft_mem_cutoff ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := A.columnControl_subset hb Hb (Finset.range (N + 1))
    (fun j => m + 1 + j) (by intro i _ j _ he; dsimp only at he; omega) hv
  push_cast at HH
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HH hK

theorem normalRightHigh_sq_le {a b v : V} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hL : 0 ≤ L) (Ha : A.ColumnControl a d N K) (Hb : U.AdjointColumnControl b e N L) :
    ‖A.normalRightHigh a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  let s := (Finset.range (N + 1)).filter (fun j => m ≤ j)
  have H := SharpColumns.row_sq_le s
    (fun j => A.physicalMode b e ((m : ℤ) - j))
    (fun j => U.adjointPhysicalMode b e ((m : ℤ) - j))
    (A.energyCutoff N) L hL (fun j _ x y => U.adjointPhysicalMode_inner hb _ x y)
    (fun w hw => by
      have HH := U.adjointColumnControl_subset hb Hb s
        (fun j => j - m) (by
          intro i hi j hj he
          dsimp only at he
          have hi := (Finset.mem_filter.mp hi).2
          have hj := (Finset.mem_filter.mp hj).2
          omega) hw
      calc
        _ = ∑ j ∈ s, ‖U.adjointPhysicalMode b e (-((j - m : ℕ) : ℤ)) w‖^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj := (Finset.mem_filter.mp hj).2
          rw [show (m : ℤ) - j = -((j - m : ℕ) : ℤ) by omega]
        _ ≤ _ := HH)
    (fun j => A.physicalMode a d j v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalRightHigh, s] using A.normalRightHigh_mem_cutoff ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := A.columnControl_subset ha Ha s id (by intro i _ j _ h; exact h) hv
  calc
    _ ≤ L * (K * ‖v‖^2) := mul_le_mul_of_nonneg_left HH hL
    _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace SharpColumns
variable {V : Type*} [NormedAddCommGroup V]

theorem norm_add_add_sub_sq_le (x y z t : V) :
    ‖x + y + z - t‖^2 ≤ 4 * (‖x‖^2 + ‖y‖^2 + ‖z‖^2 + ‖t‖^2) := by
  have h := finite_sum_sq_le_card (Finset.univ : Finset (Fin 4)) ![x, y, z, -t]
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

theorem sum_columns_sq_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → κ → V) (K : ι → ℝ)
    (H : ∀ i ∈ s, ∑ k ∈ t, ‖f i k‖^2 ≤ K i) :
    (∑ k ∈ t, ‖∑ i ∈ s, f i k‖^2) ≤ (s.card : ℝ) * ∑ i ∈ s, K i := by
  calc
    _ ≤ ∑ k ∈ t, (s.card : ℝ) * ∑ i ∈ s, ‖f i k‖^2 :=
      Finset.sum_le_sum fun k _ => finite_sum_sq_le_card s (fun i => f i k)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑ k ∈ t, ‖f i k‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum H) (Nat.cast_nonneg _)

end SharpColumns

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem normalRightLow_column_sq_le {a b v : V} {d e N : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hL : 0 ≤ L) (Ha : A.ColumnControl a d N K) (Hb : A.ColumnControl b e N L) :
    (∑ m ∈ Finset.range (N + 1), ‖A.normalRightLow a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
  classical
  have H := SharpColumns.triangular_column_sq_le (Finset.range (N + 1)) (Finset.range (N + 1))
    (fun j => A.physicalMode a d j v) (fun m j => A.physicalMode b e ((m : ℤ) - j))
    (fun m j => j < m) (fun _ _ => 1) 1 L
    (by intro m _ j _ _; simp)
    (by
      intro j hj
      have hmem := A.physicalMode_mem_cutoff ha hv j (M := N) (by omega)
      have HH := A.columnControl_subset hb Hb ((Finset.range (N + 1)).filter (fun m => j < m))
        (fun m => m - j) (by
          intro r hr s hs he
          dsimp only at he
          have hr := (Finset.mem_filter.mp hr).2
          have hs := (Finset.mem_filter.mp hs).2
          omega) hmem
      calc
        _ = ∑ m ∈ Finset.range (N + 1) with j < m,
            ‖A.physicalMode b e ((m - j : ℕ) : ℤ) (A.physicalMode a d j v)‖^2 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_filter.mp hm).2)]
        _ ≤ _ := HH)
  simp only [one_smul, one_pow, mul_one, Finset.card_range, Nat.cast_add, Nat.cast_one] at H
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left (Ha v hv)
    (mul_nonneg (by positivity : 0 ≤ (N + 1 : ℝ)) hL)
  simpa only [normalRightLow, mul_assoc, mul_comm K L, mul_left_comm L K] using HH

 

theorem normal_product_cutoff_split {a b v : V} {d e N : ℕ}
    (hb : b ∈ A.grade e) (ha : a ∈ A.grade d) (hv : v ∈ A.energyCutoff N)
    (hd : 1 ≤ d) (m : ℕ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) m v =
      A.normalLeft a b v d e N m + A.normalRightHigh a b v d e N m +
      A.normalRightLow a b v d e N m -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          (m + d + e - 2 - j) v := by
  classical
  rw [A.physical_normal_product_resplit a b v d e hd m]
  have hL : Function.support (fun j : ℕ => A.physicalMode a d (-1 - j)
      (A.physicalMode b e (m + 1 + j) v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change A.physicalMode a d (-1 - j) (A.physicalMode b e (m + 1 + j) v) = 0
    rw [A.physicalMode_zero_above_cutoff hb hv (m + 1 + j) (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => A.physicalMode b e ((m : ℤ) - j)
      (A.physicalMode a d j v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change A.physicalMode b e ((m : ℤ) - j) (A.physicalMode a d j v) = 0
    rw [A.physicalMode_zero_above_cutoff ha hv j (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
    (fun j => m ≤ j) (fun j => A.physicalMode b e ((m : ℤ) - j) (A.physicalMode a d j v))
  simp only [not_le] at hs
  dsimp only [normalLeft, normalRightHigh, normalRightLow]
  rw [← hs]
  simp only [add_assoc]

 
def sharpCorrectionMass (d : ℕ) : ℝ :=
  (d - 1 : ℕ) * ∑ i ∈ Finset.range (d - 1), (i + 1 : ℝ) *
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2

theorem sharpCorrectionMass_nonneg (d : ℕ) : 0 ≤ sharpCorrectionMass d := by
  unfold sharpCorrectionMass
  positivity

theorem singular_correction_column_sq_le {a b v : V} {d e N : ℕ} {R : ℝ}
    (hd : 1 ≤ d) (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R)
    (hv : v ∈ A.energyCutoff N) :
    (∑ m ∈ Finset.range (N + 1), ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v‖^2) ≤
      sharpCorrectionMass d * R * ‖v‖^2 := by
  classical
  let T := fun (i j m : ℕ) => (i.choose j : ℂ) •
    mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
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

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem columnControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : A.ColumnControl a d N K) (hKL : K ≤ L) : A.ColumnControl a d N L := by
  intro v hv
  exact (H v hv).trans (mul_le_mul_of_nonneg_right hKL (sq_nonneg _))

theorem columnControl_mode_sq_le {a v : V} {d N m : ℕ} {K : ℝ}
    (ha : a ∈ A.grade d) (H : A.ColumnControl a d N K) (hv : v ∈ A.energyCutoff N) :
    ‖A.physicalMode a d m v‖^2 ≤ K * ‖v‖^2 := by
  simpa using A.columnControl_subset ha H {m} id (by intro i _ j _ h; exact h) hv

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalProduct_columnControl {a b : V} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.ColumnControl a d N K) (Ha' : U.AdjointColumnControl a d N K)
    (Hb : A.ColumnControl b e N L) (Hb' : U.AdjointColumnControl b e N L)
    (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R) :
    A.ColumnControl (mode A.fields a (-1) b) (d + e) N
      (12 * (N + 1 : ℝ) * K * L + 4 * sharpCorrectionMass d * R) := by
  intro v hv
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft : (∑ m ∈ Finset.range (N + 1), ‖A.normalLeft a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => U.normalLeft_sq_le ha hb hv hK Ha' Hb
      _ = _ := by simp [mul_assoc]
  have hhigh : (∑ m ∈ Finset.range (N + 1), ‖A.normalRightHigh a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => U.normalRightHigh_sq_le ha hb hv hL Ha Hb'
      _ = _ := by simp [mul_assoc]
  have hlow := A.normalRightLow_column_sq_le ha hb hv hL Ha Hb
  have hsing := A.singular_correction_column_sq_le hd Hsing hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 4 * (‖A.normalLeft a b v d e N m‖^2 +
      ‖A.normalRightHigh a b v d e N m‖^2 + ‖A.normalRightLow a b v d e N m‖^2 + ‖T m‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      rw [A.normal_product_cutoff_split hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ = 4 * ((∑ m ∈ Finset.range (N + 1), ‖A.normalLeft a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖A.normalRightHigh a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖A.normalRightLow a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖T m‖^2)) := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]
    _ ≤ _ := by dsimp only [T] at *; nlinarith

theorem normalProduct_zero_sq_le {a b v : V} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hv : v ∈ A.energyCutoff N) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.ColumnControl a d N K) (Ha' : U.AdjointColumnControl a d N K)
    (Hb : A.ColumnControl b e N L) (Hb' : U.AdjointColumnControl b e N L)
    (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R) :
    ‖A.physicalMode (mode A.fields a (-1) b) (d + e) 0 v‖^2 ≤
      (8 * K * L + 4 * sharpCorrectionMass d * R) * ‖v‖^2 := by
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft := U.normalLeft_sq_le (m := 0) ha hb hv hK Ha' Hb
  have hhigh := U.normalRightHigh_sq_le (m := 0) ha hb hv hL Ha Hb'
  have hlow : A.normalRightLow a b v d e N 0 = 0 := by simp [normalRightLow]
  have hsing : ‖T 0‖^2 ≤ sharpCorrectionMass d * R * ‖v‖^2 := by
    apply (Finset.single_le_sum (f := fun m => ‖T m‖^2) (fun _ _ => sq_nonneg _) (by simp : 0 ∈ Finset.range (N + 1))).trans
    exact A.singular_correction_column_sq_le hd Hsing hv
  calc
    _ ≤ 4 * (‖A.normalLeft a b v d e N 0‖^2 + ‖A.normalRightHigh a b v d e N 0‖^2 +
      ‖A.normalRightLow a b v d e N 0‖^2 + ‖T 0‖^2) := by
      rw [show (0 : ℤ) = (0 : ℕ) by rfl, A.normal_product_cutoff_split hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ ≤ _ := by rw [hlow, norm_zero, zero_pow (by decide : 2 ≠ 0)]; nlinarith

end UnitaryStructure
end CFTTypeVOA

namespace SharpColumns
variable {V : Type*} [NormedAddCommGroup V]
theorem norm_add_sq_le_two (x y : V) : ‖x + y‖^2 ≤ 2 * (‖x‖^2 + ‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
end SharpColumns

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

def ColumnGrowth (X : ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N, A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q)

 

def ZeroGrowth (X : ℕ → ℝ) (a : V) (d p q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N v, v ∈ A.energyCutoff N →
    ‖A.physicalMode a d 0 v‖^2 ≤ C * (N + 1 : ℝ)^p * X N^q * ‖v‖^2

theorem columnGrowth_zero (X : ℕ → ℝ) (d p q : ℕ) : A.ColumnGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro N v hv
  simp [physicalMode, mode_zero]

theorem zeroGrowth_zero (X : ℕ → ℝ) (d p q : ℕ) : A.ZeroGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro N v hv
  simp [physicalMode, mode_zero]

theorem columnGrowth_add {X : ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q) (Hb : A.ColumnGrowth X b d p q) :
    A.ColumnGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro N v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 2 * (‖A.physicalMode a d m v‖^2 + ‖A.physicalMode b d m v‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      simp only [physicalMode, mode_add, LinearMap.add_apply]
      exact SharpColumns.norm_add_sq_le_two _ _
    _ = 2 * ((∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) +
        ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode b d m v‖^2) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by nlinarith [HC N v hv, HD N v hv]

theorem zeroGrowth_add {X : ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : A.ZeroGrowth X a d p q) (Hb : A.ZeroGrowth X b d p q) :
    A.ZeroGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro N v hv
  have h := SharpColumns.norm_add_sq_le_two (A.physicalMode a d 0 v) (A.physicalMode b d 0 v)
  simp only [physicalMode, mode_add, LinearMap.add_apply]
  dsimp only [physicalMode] at h HC HD
  nlinarith [HC N v hv, HD N v hv]

theorem columnGrowth_smul {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q) (z : ℂ) : A.ColumnGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    ← Finset.mul_sum, mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg ‖z‖)

theorem zeroGrowth_smul {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : A.ZeroGrowth X a d p q) (z : ℂ) : A.ZeroGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg ‖z‖)

theorem columnGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q p' q' : ℕ}
    (H : A.ColumnGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    A.ColumnGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, fun N => A.columnControl_mono (HC N) ?_⟩
  have hXN := zero_le_one.trans (hX N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX N

theorem zeroGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q p' q' : ℕ}
    (H : A.ZeroGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    A.ZeroGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro N v hv
  apply (HC N v hv).trans
  have hXN := zero_le_one.trans (hX N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX N

theorem zeroGrowth_of_columnGrowth {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (ha : a ∈ A.grade d) (H : A.ColumnGrowth X a d p q) : A.ZeroGrowth X a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  exact ⟨C, hC, fun N v hv => A.columnControl_mode_sq_le ha (HC N) hv (m := 0)⟩

 

def SharpDegreeGrowth (X : ℕ → ℝ) (a : V) (d w : ℕ) : Prop :=
  A.ColumnGrowth X a d (2*d-1) (2*w) ∧ A.ZeroGrowth X a d (max 1 (2*d-2)) (2*w)

def SharpGrowth (X : ℕ → ℝ) (a : V) (d : ℕ) : Prop :=
  A.SharpDegreeGrowth X a d d

def sharpGrowthSubmodule (X : ℕ → ℝ) (d : ℕ) : Submodule ℂ V where
  carrier := {a | A.SharpGrowth X a d}
  zero_mem' := ⟨A.columnGrowth_zero X d _ _, A.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨A.columnGrowth_add h.1 k.1, A.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨A.columnGrowth_smul h.1 z, A.zeroGrowth_smul h.2 z⟩

theorem finite_columnGrowth_uniform {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, A.ColumnGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ N,
      A.ColumnControl (a i) (d i) N (C * (N + 1 : ℝ)^p * X N^q) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj N
    have hXN := zero_le_one.trans (hX N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply A.columnControl_mono (HC N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply A.columnControl_mono (HD j hj N)
      gcongr
      exact le_add_of_nonneg_left hC

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
