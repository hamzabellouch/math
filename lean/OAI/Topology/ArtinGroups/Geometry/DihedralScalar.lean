import Mathlib
import OAI.Topology.ArtinGroups.Geometry.Cartan

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def dihedralScalar (m n : ℕ) : ℝ :=
  if m = 0 then (n : ℝ) else Real.sin ((n : ℝ) * (Real.pi / m)) / Real.sin (Real.pi / m)

noncomputable def dihedralWeight (m : ℕ) : ℝ :=
  if m = 0 then 2 else 2 * Real.cos (Real.pi / m)

@[simp] lemma dihedralScalar_zero (m : ℕ) : dihedralScalar m 0 = 0 := by
  simp [dihedralScalar]

@[simp] lemma dihedralScalar_one (m : ℕ) (hm : m = 0 ∨ 2 ≤ m) : dihedralScalar m 1 = 1 := by
  rcases hm with rfl | hm
  · simp [dihedralScalar]
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hang : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos hmpos
    have hlt : Real.pi / (m : ℝ) < Real.pi := by
      apply (div_lt_iff₀ hmpos).mpr
      have hmone : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      nlinarith [Real.pi_pos]
    have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hang hlt)
    simp only [dihedralScalar, ite_eq_right (by omega : m ≠ 0), Nat.cast_one, one_mul, div_self hs]

lemma dihedralScalar_recurrence (m n : ℕ) :
    dihedralScalar m (n+2) = dihedralWeight m * dihedralScalar m (n+1) - dihedralScalar m n := by
  by_cases hm : m = 0
  · simp [dihedralScalar, dihedralWeight, hm]
    ring
  · have hsin : Real.sin (((n : ℝ)+2)*(Real.pi/m)) =
        2*Real.cos (Real.pi/m)*Real.sin (((n : ℝ)+1)*(Real.pi/m)) -
          Real.sin ((n : ℝ)*(Real.pi/m)) := by
      have h := Real.sin_add ( ((n : ℝ)+1)*(Real.pi/m)) (Real.pi/m)
      have h' := Real.sin_sub ( ((n : ℝ)+1)*(Real.pi/m)) (Real.pi/m)
      rw [show ((n : ℝ)+1)*(Real.pi/m)+(Real.pi/m)=((n : ℝ)+2)*(Real.pi/m) by ring] at h
      rw [show ((n : ℝ)+1)*(Real.pi/m)-(Real.pi/m)=(n : ℝ)*(Real.pi/m) by ring] at h'
      nlinarith
    simp only [dihedralScalar, dihedralWeight, ite_eq_right hm, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [hsin]
    ring

lemma dihedralScalar_nonneg (m n : ℕ) (hn : m = 0 ∨ n ≤ m) : 0 ≤ dihedralScalar m n := by
  by_cases hm : m = 0
  · simp [dihedralScalar, hm]
  · have hn : n ≤ m := hn.resolve_left hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hpos : 0 ≤ Real.pi / (m : ℝ) := (div_pos Real.pi_pos hmpos).le
    have hle : Real.pi / (m : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hmpos).mpr
      have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith [Real.pi_pos]
    have hxpos : 0 ≤ (n : ℝ)*(Real.pi/m) := mul_nonneg (Nat.cast_nonneg _) hpos
    have hxle : (n : ℝ)*(Real.pi/m) ≤ Real.pi := by
      have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
      calc
        _ ≤ (m : ℝ)*(Real.pi/m) := mul_le_mul_of_nonneg_right hn' hpos
        _ = Real.pi := mul_div_cancel₀ _ (ne_of_gt hmpos)
    simpa only [dihedralScalar, ite_eq_right hm] using
      div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hxpos hxle)
        (Real.sin_nonneg_of_nonneg_of_le_pi hpos hle)

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

omit [Fintype S] in
lemma cartan_off_weight (i j : S) (hij : i ≠ j) :
    cartan M i j = -dihedralWeight (M i j) := by
  simp only [cartan, ite_eq_right hij, dihedralWeight]
  split_ifs <;> ring

lemma simpleReflection_basis_self (i : S) :
    simpleReflection M i (Pi.single i 1) = -(Pi.single i 1) := by
  rw [simpleReflection_apply, ← rootRow_apply, rootRow_single, cartan_diag]
  module

lemma simpleReflection_basis_other (i j : S) (hij : i ≠ j) :
    simpleReflection M i (Pi.single j 1) =
      Pi.single j 1 + dihedralWeight (M i j) • Pi.single i 1 := by
  rw [simpleReflection_apply, ← rootRow_apply, rootRow_single, cartan_off_weight i j hij]
  module

end HarmonicArtin.Geometric

end OAI
