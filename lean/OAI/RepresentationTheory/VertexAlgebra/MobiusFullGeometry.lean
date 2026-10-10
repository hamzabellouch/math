import OAI.RepresentationTheory.VertexAlgebra.MobiusExistence

namespace OAI

noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
 
def polarPhase (M : SL(2,ℝ)) : ℂ :=
  ((M 0 0+M 1 1:ℝ):ℂ)+((M 1 0-M 0 1:ℝ):ℂ)*Complex.I
lemma polarPhase_ne_zero (M : SL(2,ℝ)) : polarPhase M ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [polarPhase] at hr hi
  have hd := det M
  have he : M 1 1 = -M 0 0 := by linarith
  have hf : M 1 0 = M 0 1 := by linarith
  rw [he,hf] at hd
  nlinarith [sq_nonneg (M 0 0),sq_nonneg (M 0 1)]
def polarAngle (M : SL(2,ℝ)) : ℝ := 2*(polarPhase M).arg
lemma polar_cos (M : SL(2,ℝ)) :
    Real.cos (polarAngle M/2)=(M 0 0+M 1 1)/‖polarPhase M‖ := by
  rw [polarAngle,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),Complex.cos_arg (polarPhase_ne_zero M)]
  simp [polarPhase]
lemma polar_sin (M : SL(2,ℝ)) :
    Real.sin (polarAngle M/2)=(M 1 0-M 0 1)/‖polarPhase M‖ := by
  rw [polarAngle,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),Complex.sin_arg]
  simp [polarPhase]
lemma polar_dot_identity (M : SL(2,ℝ)) (x : ℝ) :
    ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x=
      (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))^2+
      (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))^2+1 := by
  have hn : ‖polarPhase M‖ ≠ 0 := norm_ne_zero_iff.mpr (polarPhase_ne_zero M)
  have he : ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x=
      (M 0 0*Real.cos (x/2)+M 0 1*Real.sin (x/2))^2+
      (M 1 0*Real.cos (x/2)+M 1 1*Real.sin (x/2))^2+
      (M 0 0*M 1 1-M 0 1*M 1 0)*(Real.cos (x/2)^2+Real.sin (x/2)^2) := by
    have h00 : ((rotationMatrix (polarAngle M))⁻¹*M) 0 0 =
        Real.cos (polarAngle M/2)*M 0 0+Real.sin (polarAngle M/2)*M 1 0 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h01 : ((rotationMatrix (polarAngle M))⁻¹*M) 0 1 =
        Real.cos (polarAngle M/2)*M 0 1+Real.sin (polarAngle M/2)*M 1 1 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h10 : ((rotationMatrix (polarAngle M))⁻¹*M) 1 0 =
        -Real.sin (polarAngle M/2)*M 0 0+Real.cos (polarAngle M/2)*M 1 0 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    have h11 : ((rotationMatrix (polarAngle M))⁻¹*M) 1 1 =
        -Real.sin (polarAngle M/2)*M 0 1+Real.cos (polarAngle M/2)*M 1 1 := by
      change (Matrix.adjugate !![Real.cos (polarAngle M/2),-Real.sin (polarAngle M/2);
        Real.sin (polarAngle M/2),Real.cos (polarAngle M/2)] * (M : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = _
      simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    simp only [dot,h00,h01,h10,h11,polar_cos,polar_sin]
    field_simp [hn]
    ring
  rw [he,det,cos_sq_add_sin_sq]
  ring
lemma polar_dot_positive (M : SL(2,ℝ)) :
    ∀ x, 0 < dot ((rotationMatrix (polarAngle M))⁻¹*M) x := by
  intro x
  have h : 0 < ‖polarPhase M‖*dot ((rotationMatrix (polarAngle M))⁻¹*M) x := by
    rw [polar_dot_identity]
    positivity
  exact pos_of_mul_pos_right h (norm_nonneg _)
 

theorem exists_implements (M : SL(2,ℝ)) : ∃ F : SmoothCircleLift, Implements M F := by
  let B := (rotationMatrix (polarAngle M))⁻¹*M
  let G := positiveLift B (polar_dot_positive M)
  refine ⟨SmoothCircleLift.rotation (polarAngle M)*G,?_⟩
  have h := implements_mul (implements_rotation (polarAngle M))
    (implements_positiveLift B (polar_dot_positive M))
  simpa only [B,mul_inv_cancel_left] using h
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
