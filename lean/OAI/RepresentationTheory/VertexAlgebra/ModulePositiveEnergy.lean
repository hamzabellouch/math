import OAI.RepresentationTheory.VertexAlgebra.ModuleAdjoints

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {M : A.GradingRestrictedModule W} (R : M.UnitaryStructure U)
include R

 
theorem lowering_ne_zero {z : ℂ} {x : W} (hx : x ∈ M.grade z)
    (hz : z.re < 0) (hne : x ≠ 0) : M.virasoroMode 1 x ≠ 0 := by
  intro he
  have h := R.sl2_norm_difference hx
  rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  have hp : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hn : 2*z.re*‖x‖^2 < 0 := mul_neg_of_neg_of_pos (by linarith) hp
  exact (not_lt_of_ge (sq_nonneg _)) (h ▸ hn)

 

theorem weight_nonneg {z : ℂ} {x : W} (hx : x ∈ M.grade z) (hne : x ≠ 0) :
    0 ≤ z.re := by
  by_contra hn
  have hz : z.re < 0 := lt_of_not_ge hn
  have hi (n : ℕ) : (M.virasoroMode 1 ^ n) x ∈ M.grade (z-(n:ℂ)) ∧
      (M.virasoroMode 1 ^ n) x ≠ 0 := by
    induction n with
    | zero => simpa using And.intro hx hne
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      constructor
      · have h := M.virasoro_mem_grade ih.1 1
        convert h using 1
        push_cast
        ring_nf
      · apply R.lowering_ne_zero ih.1 _ ih.2
        simp only [Complex.sub_re, Complex.natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N,hN⟩ := M.lower_truncated z
  have h := (hi N).1
  rw [hN N le_rfl, Submodule.mem_bot] at h
  exact (hi N).2 h

 
theorem grade_eq_bot_of_negative {z : ℂ} (hz : z.re < 0) : M.grade z=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  by_contra hne
  exact (not_lt_of_ge (R.weight_nonneg hx hne)) hz

theorem grade_eq_bot_of_nonreal {z : ℂ} (hz : (z.re:ℂ) ≠ z) : M.grade z=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  by_contra hne
  exact hz (R.weight_real hx hne)

 
theorem physicalMode_eq_zero_of_negative {d : ℕ} {a : V} (ha : a ∈ A.grade d)
    {z : ℂ} {x : W} (hx : x ∈ M.grade z) (m : ℤ) (hm : z.re < m) :
    M.physicalMode a d m x=0 := by
  have h := M.physicalMode_mem_grade ha hx m
  rw [R.grade_eq_bot_of_negative (by simp only [Complex.sub_re, Complex.intCast_re]; linarith),
    Submodule.mem_bot] at h
  exact h

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule.UnitaryStructure

end

end OAI
