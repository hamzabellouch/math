import OAI.RepresentationTheory.VertexAlgebra.ModuleMobiusAlgebra

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)
include R
theorem physicalMode_adjoint {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (m : ℤ) (b c : W) :
    inner ℂ (M.physicalMode a d m b) c =
      inner ℂ b (M.physicalMode a d (-m) c) := by
  have hp : A.virasoroMode 1 (U.pct a) = 0 := U.pct_quasiPrimary hq
  have hpj (j : ℕ) (hj : j ≠ 0) :
      (A.virasoroMode 1 ^ j) (U.pct a) = 0 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hp, map_zero]
  have hs :
      (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
        mode M.fields ((A.virasoroMode 1 ^ j) (U.pct a))
          (2 * (d : ℤ) - j - (m + d - 1) - 2) c) =
      mode M.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hpj j hj]
    · simp
  have h := R.invariant d a ha (m + d - 1) b c
  rw [hs] at h
  have he :
      ((-1 : ℂ)^d) •
        mode M.fields (U.pct a) (2 * (d : ℤ) - (m + d - 1) - 2) c =
      mode M.fields a (2 * (d : ℤ) - (m + d - 1) - 2) c := by
    rw [← LinearMap.smul_apply, ← mode_smul, hh]
  rw [he] at h
  have hi : 2 * (d : ℤ) - (m + d - 1) - 2 = -m + d - 1 := by omega
  simpa only [physicalMode, hi] using h

 
theorem virasoro_adjoint (m : ℤ) (x y : W) :
    inner ℂ (M.virasoroMode m x) y=inner ℂ x (M.virasoroMode (-m) y) := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [CFTTypeVOA.UnitaryStructure.IsHermitian, U.pct_conformal]
  simpa using R.physicalMode_adjoint A.conformal_mem A.conformal_quasiPrimary hh m x y

 
theorem weight_real {z : ℂ} {x : W} (hx : x ∈ M.grade z) (hne : x ≠ 0) :
    (z.re : ℂ)=z := by
  have h := R.virasoro_adjoint 0 x x
  simp only [neg_zero, M.virasoro_zero_on_grade hx, inner_smul_left, inner_smul_right] at h
  exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ (inner_self_ne_zero.mpr hne) h)

 
theorem grades_orthogonal {z w : ℂ} (hzw : z ≠ w) {x y : W}
    (hx : x ∈ M.grade z) (hy : y ∈ M.grade w) : inner ℂ x y=0 := by
  by_cases hnx : x=0
  · simp [hnx]
  have hz := R.weight_real hx hnx
  have hzbar : starRingEnd ℂ z = z := Complex.conj_eq_iff_re.mpr hz
  have h := R.virasoro_adjoint 0 x y
  simp only [neg_zero, M.virasoro_zero_on_grade hx, M.virasoro_zero_on_grade hy,
    inner_smul_left, inner_smul_right, hzbar] at h
  have hne : z-w ≠ 0 := sub_ne_zero.mpr hzw
  apply (mul_eq_zero.mp (show (z-w)*inner ℂ x y=0 from ?_)).resolve_left hne
  rw [sub_mul, h, sub_self]

 
theorem sl2_norm_difference {z : ℂ} {x : W} (hx : x ∈ M.grade z) :
    ‖M.virasoroMode (-1) x‖^2-‖M.virasoroMode 1 x‖^2=2*z.re*‖x‖^2 := by
  have h := congrArg (fun y : W => (inner ℂ x y).re) (M.sl2_commutator x)
  have hm := R.virasoro_adjoint (-1) x (M.virasoroMode (-1) x)
  have hp := R.virasoro_adjoint 1 x (M.virasoroMode 1 x)
  norm_num only [neg_neg] at hm
  rw [inner_sub_right, Complex.sub_re, ← hm, ← hp,
    M.virasoro_zero_on_grade hx] at h
  simpa [inner_smul_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.mul_re, mul_assoc] using h

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
