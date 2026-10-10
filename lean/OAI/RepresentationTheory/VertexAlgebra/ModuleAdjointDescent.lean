import OAI.RepresentationTheory.VertexAlgebra.ModuleCommutatorBounds

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (Q : M.UnitaryStructure U)
include Q
theorem mode_norm_sq_difference {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : W) :
    ‖M.physicalMode a d (-m) c‖ ^ 2 - ‖M.physicalMode a d m c‖ ^ 2 =
      (inner ℂ c (M.selfCommutator a d m c)).re := by
  have hp := Q.physicalMode_adjoint ha hq hh (-m) c (M.physicalMode a d (-m) c)
  simp only [neg_neg] at hp
  have hn := Q.physicalMode_adjoint ha hq hh m c (M.physicalMode a d m c)
  rw [selfCommutator_apply, inner_sub_right, ← hp, ← hn, Complex.sub_re]
  exact (congrArg₂ (fun x y : ℝ => x - y)
    (inner_self_eq_norm_sq (𝕜 := ℂ) (M.physicalMode a d (-m) c))
    (inner_self_eq_norm_sq (𝕜 := ℂ) (M.physicalMode a d m c))).symm

 
theorem mode_norm_sq_le_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) (c : W) :
    ‖M.physicalMode a d m c‖ ^ 2 ≤
      ‖c‖ * ‖M.physicalMode a d (-m) (M.physicalMode a d m c)‖ := by
  have h := congrArg Complex.re
    (Q.physicalMode_adjoint ha hq hh m c (M.physicalMode a d m c))
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact h.trans_le ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))

 

theorem lowering_norm_sq_of_commutator (t : EnergyBand) {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ M.bandGrade t h, ‖M.selfCommutator a d m c‖ ≤ R * ‖c‖) :
    ∀ h ≤ N, ∀ c ∈ M.bandGrade t h,
      ‖M.physicalMode a d m c‖ ^ 2 ≤ (h : ℝ) * R * ‖c‖ ^ 2 := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hN c hc
    by_cases hhm : h < m
    · have hz : M.physicalMode a d m c = 0 :=
        Q.physicalMode_eq_zero_above_band t ha hc m (by omega)
      rw [hz, norm_zero, zero_pow (by omega)]
      positivity
    · let e := h - m
      have heh : e < h := by dsimp [e]; omega
      have heN : e ≤ N := by omega
      have hb : M.physicalMode a d m c ∈ M.bandGrade t e :=
        M.mode_mem_band t ha hc ((m : ℤ) + d - 1) (by dsimp [e]; omega)
      have hi := ih e heh heN _ hb
      have hcom : (inner ℂ (M.physicalMode a d m c)
          (M.selfCommutator a d m (M.physicalMode a d m c))).re ≤
          R * ‖M.physicalMode a d m c‖ ^ 2 := by
        calc
          _ ≤ ‖inner ℂ (M.physicalMode a d m c)
              (M.selfCommutator a d m (M.physicalMode a d m c))‖ := Complex.re_le_norm _
          _ ≤ ‖M.physicalMode a d m c‖ *
              ‖M.selfCommutator a d m (M.physicalMode a d m c)‖ := norm_inner_le_norm _ _
          _ ≤ ‖M.physicalMode a d m c‖ * (R * ‖M.physicalMode a d m c‖) := by
            gcongr
            exact H e heN _ hb
          _ = _ := by ring
      have hdiff := Q.mode_norm_sq_difference ha hq hh (m : ℤ) (M.physicalMode a d m c)
      have hecast : (e : ℝ) + 1 ≤ h := by exact_mod_cast (by omega : e + 1 ≤ h)
      have hraise : ‖M.physicalMode a d (-(m : ℤ)) (M.physicalMode a d m c)‖ ^ 2 ≤
          (h : ℝ) * R * ‖M.physicalMode a d m c‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hecast
          (mul_nonneg hR (sq_nonneg ‖M.physicalMode a d m c‖))
        nlinarith
      have hcs := Q.mode_norm_sq_le_adjoint ha hq hh (m : ℤ) c
      by_cases hz : ‖M.physicalMode a d m c‖ = 0
      · rw [hz, zero_pow (by omega)]
        positivity
      · have hp : 0 < ‖M.physicalMode a d m c‖ ^ 2 := sq_pos_of_ne_zero hz
        apply (mul_le_mul_iff_of_pos_right hp).mp
        calc
          _ ≤ (‖c‖ * ‖M.physicalMode a d (-(m : ℤ)) (M.physicalMode a d m c)‖) ^ 2 := by
            nlinarith [sq_nonneg (‖c‖ * ‖M.physicalMode a d (-(m : ℤ)) (M.physicalMode a d m c)‖ -
              ‖M.physicalMode a d m c‖ ^ 2)]
          _ = ‖c‖ ^ 2 * ‖M.physicalMode a d (-(m : ℤ)) (M.physicalMode a d m c)‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖c‖ ^ 2 * ((h : ℝ) * R * ‖M.physicalMode a d m c‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hraise (sq_nonneg _)
          _ = _ := by ring

 

theorem raising_norm_sq_of_commutator (t : EnergyBand) {a : V} {d m N : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R)
    (H : ∀ h ≤ N, ∀ c ∈ M.bandGrade t h, ‖M.selfCommutator a d m c‖ ≤ R * ‖c‖)
    {h : ℕ} (hN : h ≤ N) {c : W} (hc : c ∈ M.bandGrade t h) :
    ‖M.physicalMode a d (-(m : ℤ)) c‖ ^ 2 ≤ ((h : ℝ) + 1) * R * ‖c‖ ^ 2 := by
  have hi := Q.lowering_norm_sq_of_commutator t ha hq hh hm hR H h hN c hc
  have hdiff := Q.mode_norm_sq_difference ha hq hh (m : ℤ) c
  have hcom : (inner ℂ c (M.selfCommutator a d m c)).re ≤ R * ‖c‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ c (M.selfCommutator a d m c)‖ := Complex.re_le_norm _
      _ ≤ ‖c‖ * ‖M.selfCommutator a d m c‖ := norm_inner_le_norm _ _
      _ ≤ ‖c‖ * (R * ‖c‖) := mul_le_mul_of_nonneg_left (H h hN c hc) (norm_nonneg _)
      _ = _ := by ring
  nlinarith

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
