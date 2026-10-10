import OAI.RepresentationTheory.VertexAlgebra.ModuleBlockGrowth

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

theorem zeroMode_commutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (x : W) :
    M.virasoroMode 1 (M.physicalMode a d (-1) x) -
      M.physicalMode a d (-1) (M.virasoroMode 1 x) =
        (d:ℂ) • M.physicalMode a d 0 x := by
  have h := congrArg (fun f : Module.End ℂ W => f x)
    (M.virasoro_one_physical_commutator ha hq (-1))
  simpa using h
def selfCommutator (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ W :=
  M.physicalMode a d m * M.physicalMode a d (-m) -
    M.physicalMode a d (-m) * M.physicalMode a d m

@[simp]
theorem selfCommutator_apply (a : V) (d : ℕ) (m : ℤ) (c : W) :
    M.selfCommutator a d m c =
      M.physicalMode a d m (M.physicalMode a d (-m) c) -
        M.physicalMode a d (-m) (M.physicalMode a d m c) := rfl

 

theorem selfCommutator_eq_sum {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (c : W) :
    M.selfCommutator a d m c =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        M.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c := by
  have hm : ((m + d - 1 : ℕ) : ℤ) = (m : ℤ) + d - 1 := by omega
  simp only [selfCommutator_apply, physicalMode]
  rw [← hm, M.toWeakModule.mode_commutator]
  simp only [Int.cast_natCast, Ring.choose_natCast]
  have he : (∑ᶠ j : ℕ, ((m + d - 1).choose j : ℂ) •
      mode M.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c) =
      ∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
        mode M.fields (mode A.fields a j a) ((m + d - 1 : ℕ) + (-(m : ℤ) + d - 1) - j) c := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hjn
    have hz := A.mode_eq_zero_of_negative_energy ha ha (j : ℤ) (by omega)
    apply hj
    simp only [hz, mode_zero, LinearMap.zero_apply, smul_zero]
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  congr 3
  omega

 

theorem selfCommutator_eq_sum_reduced {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (v : W) :
    M.selfCommutator a d m v =
      ∑ j ∈ Finset.range (2 * d - 1),
        (((m + d - 1).choose (j + 1) : ℂ) - ((d - 1).choose (j + 1) : ℂ)) •
          M.physicalMode (mode A.fields a (j + 1) a) (2 * d - j - 2) 0 v := by
  have hzero := M.selfCommutator_eq_sum ha hd 0 v
  simp only [selfCommutator_apply, Nat.cast_zero, neg_zero, sub_self, zero_add] at hzero
  have he : 2 * d = (2 * d - 1) + 1 := by omega
  calc
    _ = (∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
          M.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v) -
        ∑ j ∈ Finset.range (2 * d), ((d - 1).choose j : ℂ) •
          M.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [M.selfCommutator_eq_sum ha hd, ← hzero, sub_zero]
    _ = ∑ j ∈ Finset.range (2 * d),
        (((m + d - 1).choose j : ℂ) - ((d - 1).choose j : ℂ)) •
          M.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [← Finset.sum_sub_distrib]
      simp only [sub_smul]
    _ = _ := by
      rw [he, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, sub_self, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      congr 3

 

theorem selfCommutator_bound {B : EnergyBand → ℕ → ℝ} (hB : ∀ t N, 1 ≤ B t N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (H : ∀ j < 2 * d, M.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - j - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ t, ∀ N m : ℕ, m ≤ N + 1 →
      ∀ h ≤ N, ∀ c ∈ M.bandGrade t h,
        ‖M.selfCommutator a d m c‖ ≤
          C * (1 + (N : ℝ)) ^ p * B t N ^ (2 * d - 1) * ‖c‖ := by
  let s := Finset.range (2 * d)
  have H' : ∀ j ∈ s, M.BlockGrowth B (mode A.fields a j a)
      (2 * d - j - 1) (2 * d - 1) := by
    intro j hj
    exact M.blockGrowth_mono_weight hB (H j (Finset.mem_range.mp hj)) (by omega)
  obtain ⟨C, hC, p, hp⟩ := M.finite_blockGrowth_uniform hB s
    (fun j => mode A.fields a j a) (fun j => 2 * d - j - 1) (fun _ => 2 * d - 1) H'
  refine ⟨(2 * d : ℝ) * ((d : ℝ) + 1) ^ (2 * d) * C, by positivity, p + 2 * d, ?_⟩
  intro t N m hm h hN c hc
  have hBN : 0 ≤ B t N := zero_le_one.trans (hB t N)
  have hN1 : 1 ≤ 1 + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hbase : 1 ≤ ((d : ℝ) + 1) * (1 + (N : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hcoef (j : ℕ) (hj : j < 2 * d) :
      ((m + d - 1).choose j : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d) := by
    have hn : (m + d - 1 : ℕ) ≤ (d + 1) * (N + 1) := by
      calc
        m + d - 1 ≤ m + d := Nat.sub_le _ _
        _ ≤ N + 1 + d := Nat.add_le_add_right hm d
        _ ≤ _ := by nlinarith
    calc
      _ ≤ ((m + d - 1 : ℕ) : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow (m + d - 1) j
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ j := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast (show m + d - 1 ≤ (d + 1) * (1 + N) by simpa only [Nat.add_comm] using hn)
      _ ≤ (((d : ℝ) + 1) * (1 + (N : ℝ))) ^ (2 * d) :=
        pow_le_pow_right₀ hbase (by omega)
      _ = _ := mul_pow _ _ _
  rw [M.selfCommutator_eq_sum ha hd]
  calc
    _ ≤ ∑ j ∈ Finset.range (2 * d), ‖((m + d - 1).choose j : ℂ) •
        M.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 c‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (2 * d),
        (((d : ℝ) + 1) ^ (2 * d) * (1 + (N : ℝ)) ^ (2 * d)) *
          (C * (1 + (N : ℝ)) ^ p * B t N ^ (2 * d - 1) * ‖c‖) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Complex.norm_natCast]
      have hmode := hp j hj t N h hN h hN c hc
      simp only [sub_self] at hmode
      exact mul_le_mul (hcoef j (Finset.mem_range.mp hj)) hmode (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rw [pow_add]; ring

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
