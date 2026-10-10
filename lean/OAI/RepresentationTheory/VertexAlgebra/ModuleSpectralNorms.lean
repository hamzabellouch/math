import OAI.RepresentationTheory.VertexAlgebra.ModuleBands

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

theorem energyShift_on_grade {z : ℂ} {x : W} (hx : x ∈ M.grade z) :
    M.energyShift x=(1+z) • x := by
  change x+M.virasoroMode 0 x=_
  rw [M.virasoro_zero_on_grade hx]
  module

theorem energyShift_pow_on_grade {z : ℂ} {x : W} (hx : x ∈ M.grade z) (k : ℕ) :
    (M.energyShift^k) x=(1+z)^k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, M.energyShift_on_grade hx,
      smul_smul, ← pow_succ]

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q

 

theorem exists_band_of_mem {z : ℂ} {x : W} (hx : x ∈ M.grade z) (hne : x ≠ 0) :
    ∃ t : EnergyBand, ∃ h : ℕ, z=(t.val:ℂ)+h := by
  have hr := Q.weight_nonneg hx hne
  have hz := Q.weight_real hx hne
  let h := Nat.floor z.re
  have hl : (h:ℝ) ≤ z.re := Nat.floor_le hr
  have hu : z.re < (h:ℝ)+1 := Nat.lt_floor_add_one z.re
  refine ⟨⟨z.re-h, by constructor <;> linarith⟩, h, ?_⟩
  change z=((z.re-(h:ℝ):ℝ):ℂ)+(h:ℂ)
  push_cast
  rw [hz]
  ring

theorem energyShift_pow_norm_on_grade {z : ℂ} {x : W}
    (hx : x ∈ M.grade z) (k : ℕ) :
    ‖(M.energyShift^k) x‖=(1+z.re)^k*‖x‖ := by
  by_cases h0 : x=0
  · simp [h0]
  rw [M.energyShift_pow_on_grade hx, norm_smul, norm_pow]
  have hz := Q.weight_real hx h0
  have hzn := Q.weight_nonneg hx h0
  have hc : 1+z=((1+z.re:ℝ):ℂ) := by rw [← hz]; push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

theorem grade_orthogonalFamily :
    OrthogonalFamily ℂ (fun z => M.grade z) (fun z => (M.grade z).subtypeₗᵢ) := by
  intro z w hzw x y
  exact Q.grades_orthogonal hzw x.property y.property

theorem norm_sq_eq_sum_grades (x : W) :
    ‖x‖^2=∑ z ∈ M.gradeSupport x, ‖M.gradeComponent z x‖^2 := by
  have h := Q.grade_orthogonalFamily.norm_sum (fun z => M.gradingEquiv x z)
    (M.gradeSupport x)
  change ‖∑ z ∈ M.gradeSupport x, M.gradeComponent z x‖^2 =
    ∑ z ∈ M.gradeSupport x, ‖M.gradeComponent z x‖^2 at h
  rwa [M.sum_gradeComponents] at h

theorem energy_norm_sq_eq_sum_grades (x : W) (k : ℕ) :
    ‖(M.energyShift^k) x‖^2=
      ∑ z ∈ M.gradeSupport x, ((1+z.re)^k*‖M.gradeComponent z x‖)^2 := by
  have h := Q.grade_orthogonalFamily.norm_sum
    (fun z => ⟨(M.energyShift^k) (M.gradeComponent z x), by
      rw [M.energyShift_pow_on_grade (M.gradeComponent_mem z x)]
      exact (M.grade z).smul_mem _ (M.gradeComponent_mem z x)⟩)
    (M.gradeSupport x)
  change ‖∑ z ∈ M.gradeSupport x, (M.energyShift^k) (M.gradeComponent z x)‖^2 =
    ∑ z ∈ M.gradeSupport x, ‖(M.energyShift^k) (M.gradeComponent z x)‖^2 at h
  rw [← map_sum, M.sum_gradeComponents] at h
  simpa only [Q.energyShift_pow_norm_on_grade (M.gradeComponent_mem _ _)] using h

theorem mode_images_orthogonal {d : ℕ} {a : V} {z w : ℂ} {x y : W}
    (ha : a ∈ A.grade d) (hx : x ∈ M.grade z) (hy : y ∈ M.grade w)
    (hzw : z ≠ w) (n : ℤ) : inner ℂ (mode M.fields a n x) (mode M.fields a n y)=0 := by
  apply Q.grades_orthogonal _ (M.mode_mem_grade ha hx n) (M.mode_mem_grade ha hy n)
  intro h
  apply hzw
  linear_combination h

theorem mode_norm_sq_eq_sum_grades {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    (n : ℤ) (x : W) :
    ‖mode M.fields a n x‖^2=
      ∑ z ∈ M.gradeSupport x, ‖mode M.fields a n (M.gradeComponent z x)‖^2 := by
  classical
  let f := fun z => mode M.fields a n (M.gradeComponent z x)
  have hsum : ∑ z ∈ M.gradeSupport x, f z=mode M.fields a n x := by
    dsimp only [f]
    rw [← map_sum, M.sum_gradeComponents]
  have h : inner ℂ (∑ z ∈ M.gradeSupport x, f z) (∑ z ∈ M.gradeSupport x, f z)=
      ∑ z ∈ M.gradeSupport x, inner ℂ (f z) (f z) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro z hz
    rw [inner_sum]
    apply Finset.sum_eq_single z
    · intro w _ hwz
      exact Q.mode_images_orthogonal ha (M.gradeComponent_mem z x)
        (M.gradeComponent_mem w x) (Ne.symm hwz) n
    · exact fun hn => (hn hz).elim
  rw [hsum] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

 
theorem energyShift_pow_norm_mono {k l : ℕ} (hkl : k ≤ l) (x : W) :
    ‖(M.energyShift^k) x‖ ≤ ‖(M.energyShift^l) x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Q.energy_norm_sq_eq_sum_grades, Q.energy_norm_sq_eq_sum_grades]
  apply Finset.sum_le_sum
  intro z _
  by_cases h0 : M.gradeComponent z x=0
  · simp [h0]
  have hz := Q.weight_nonneg (M.gradeComponent_mem z x) h0
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_right₀ (by linarith) hkl

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
