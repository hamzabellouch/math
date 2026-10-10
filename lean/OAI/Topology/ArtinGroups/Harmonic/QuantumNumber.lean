import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin

noncomputable def quantumNumber (m : ℕ) (j : ℤ) : ℝ :=
  Real.sin ((j : ℝ) * (Real.pi / m)) / Real.sin (Real.pi / m)

lemma quantumNumber_zero (m : ℕ) : quantumNumber m 0 = 0 := by
  simp [quantumNumber]

lemma quantum_denominator_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < Real.sin (Real.pi / m) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos (by exact_mod_cast (show 0 < m by omega))
  · exact div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < m by omega))

lemma quantumNumber_one {m : ℕ} (hm : 2 ≤ m) : quantumNumber m 1 = 1 := by
  simp only [quantumNumber, Int.cast_one, one_mul]
  exact div_self (ne_of_gt (quantum_denominator_pos hm))

lemma quantumNumber_end {m : ℕ} (hm : 2 ≤ m) : quantumNumber m m = 0 := by
  unfold quantumNumber
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Int.cast_natCast, mul_div_cancel₀ Real.pi hn, Real.sin_pi, zero_div]

lemma quantumNumber_pos {m : ℕ} (hm : 2 ≤ m) {j : ℤ} (hj : 0 < j) (hjm : j < m) :
    0 < quantumNumber m j := by
  unfold quantumNumber
  apply div_pos _ (quantum_denominator_pos hm)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by exact_mod_cast hj)
      (div_pos Real.pi_pos (by exact_mod_cast (show 0 < m by omega)))
  · rw [← mul_div_assoc, div_lt_iff₀ (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < m)]
    have hh : (j : ℝ) < m := by exact_mod_cast hjm
    nlinarith [Real.pi_pos]

lemma quantumNumber_recurrence (m : ℕ) (j : ℤ) :
    quantumNumber m (j-1) + quantumNumber m (j+1) =
      (2 * Real.cos (Real.pi / m)) * quantumNumber m j := by
  unfold quantumNumber
  have hminus : ((j-1 : ℤ) : ℝ) * (Real.pi / m) = (j : ℝ) * (Real.pi / m) - (Real.pi / m) := by
    push_cast; ring
  have hplus : ((j+1 : ℤ) : ℝ) * (Real.pi / m) = (j : ℝ) * (Real.pi / m) + (Real.pi / m) := by
    push_cast; ring
  rw [hminus,hplus,Real.sin_sub,Real.sin_add]
  ring

abbrev StringLabel (m : ℕ) := Fin (m-1)

noncomputable def stringWeight (m : ℕ) (j : StringLabel m) : ℝ :=
  quantumNumber m ((j.val : ℤ)+1)

def stringMultiplicity (m : ℕ) (i j : StringLabel m) : ℕ :=
  (if i.val+1=j.val then 1 else 0) + (if j.val+1=i.val then 1 else 0)

lemma stringWeight_pos {m : ℕ} (hm : 2 ≤ m) (j : StringLabel m) :
    0 < stringWeight m j := by
  apply quantumNumber_pos hm <;> have := j.isLt <;> omega

lemma stringMultiplicity_symm (m : ℕ) (i j : StringLabel m) :
    stringMultiplicity m i j = stringMultiplicity m j i := by
  unfold stringMultiplicity
  omega

lemma stringMultiplicity_diag (m : ℕ) (i : StringLabel m) :
    stringMultiplicity m i i = 0 := by simp [stringMultiplicity]

lemma stringMultiplicity_le_one (m : ℕ) (i j : StringLabel m) :
    stringMultiplicity m i j ≤ 1 := by
  unfold stringMultiplicity
  split_ifs <;> omega

lemma stringWeight_next {m : ℕ} (hm : 2 ≤ m) (i : StringLabel m) :
    (∑ j : StringLabel m, if i.val+1=j.val then stringWeight m j else 0) =
      quantumNumber m ((i.val : ℤ)+2) := by
  classical
  by_cases hi : i.val+1 < m-1
  · let k : StringLabel m := ⟨i.val+1,hi⟩
    rw [Finset.sum_eq_single k]
    · simp only [k, ite_true, stringWeight, Nat.cast_add, Nat.cast_one]
      congr 1
    · intro j _ hj
      have hh : i.val+1 ≠ j.val := by
        intro hh
        apply hj
        apply Fin.ext
        exact hh.symm
      exact ite_eq_right hh
    · intro hh
      exact (hh (Finset.mem_univ k)).elim
  · have hend : (i.val : ℤ)+2 = m := by have := i.isLt; omega
    rw [hend, quantumNumber_end hm]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    have := j.isLt
    omega

lemma stringWeight_previous {m : ℕ} (i : StringLabel m) :
    (∑ j : StringLabel m, if j.val+1=i.val then stringWeight m j else 0) =
      quantumNumber m i.val := by
  classical
  by_cases hi : 0 < i.val
  · let k : StringLabel m := ⟨i.val-1,by have := i.isLt; omega⟩
    rw [Finset.sum_eq_single k]
    · have hk : k.val+1=i.val := by simp only [k]; omega
      rw [ite_eq_left hk]
      unfold stringWeight
      congr 1
      omega
    · intro j _ hj
      apply ite_eq_right
      intro hh
      apply hj
      apply Fin.ext
      dsimp only [k]
      omega
    · intro hh
      exact (hh (Finset.mem_univ k)).elim
  · have hz : i.val = 0 := by omega
    rw [hz, Nat.cast_zero, quantumNumber_zero]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    omega

lemma string_dimension_identity {m : ℕ} (hm : 2 ≤ m) (i : StringLabel m) :
    (∑ j : StringLabel m, (stringMultiplicity m i j : ℝ) * stringWeight m j) =
      (2 * Real.cos (Real.pi / m)) * stringWeight m i := by
  simp only [stringMultiplicity, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  rw [stringWeight_next hm, stringWeight_previous, add_comm]
  have h := quantumNumber_recurrence m ((i.val : ℤ)+1)
  have h1 : (i.val : ℤ)+1-1 = i.val := by omega
  have h2 : (i.val : ℤ)+1+1 = (i.val : ℤ)+2 := by omega
  simpa only [h1, h2, stringWeight] using h

end HarmonicArtin

end OAI
