import Mathlib

namespace OAI

/-! The finite-dimensional projection calculation in the mesh argument. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped ComplexOrder
attribute [local instance] Classical.decEq
variable {I J : Type} [Fintype I] [Fintype J]

/-- The loop, adjacent, and prefix identities give the next scalar in
the projection recurrence. -/
theorem mesh_scalar_step (C D : Matrix I J ℂ) (P : Matrix I I ℂ)
    (R : Matrix J J ℂ) (delta a : ℂ)
    (hPsq : P*P=P) (hCR : C*R=P*C) (hRC : R*C.conjTranspose=C.conjTranspose*P)
    (hloop : C*C.conjTranspose=delta • (1 : Matrix I I ℂ))
    (hadj : C*D.conjTranspose=1) (hadj' : D*C.conjTranspose=1) :
    C*(R-a • (R*D.conjTranspose*D*R))*C.conjTranspose=(delta-a) • P := by
  have hfirst : C*R*C.conjTranspose=delta • P := by
    rw [hCR,Matrix.mul_assoc,hloop,Matrix.mul_smul,Matrix.mul_one]
  have hsecond : C*(R*D.conjTranspose*D*R)*C.conjTranspose=P := by
    calc
      _ = (C*R)*D.conjTranspose*D*(R*C.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = (P*C)*D.conjTranspose*D*(C.conjTranspose*P) := by rw [hCR,hRC]
      _ = P*(C*D.conjTranspose)*(D*C.conjTranspose)*P := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hadj,hadj',Matrix.mul_one,Matrix.mul_one,hPsq]
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    hfirst,hsecond,sub_smul]

/-- Removing the scaled row-space projection imposes one more contraction.
All hypotheses here are matrix identities, proved for the path operators
in the mesh construction. -/
theorem mesh_projection_correction (Q : Matrix I I ℂ) (T : Matrix J I ℂ)
    (P : Matrix J J ℂ) (lam : ℝ) (hlam : lam≠0)
    (hQstar : Q.conjTranspose=Q) (hQsq : Q*Q=Q)
    (hTQ : T*Q=T) (hTT : T*T.conjTranspose=(lam : ℂ) • P) (hPT : P*T=T) :
    let R := Q - ((lam⁻¹ : ℝ) : ℂ) • (T.conjTranspose*T)
    R.conjTranspose=R ∧ R*R=R ∧ R*Q=R ∧ T*R=0 ∧
      Matrix.trace R=Matrix.trace Q-Matrix.trace P := by
  let a : ℂ := (lam⁻¹ : ℝ)
  let B : Matrix I I ℂ := a • (T.conjTranspose*T)
  have ha : a*(lam : ℂ)=1 := by
    dsimp [a]
    rw [←Complex.ofReal_mul,inv_mul_cancel₀ hlam,Complex.ofReal_one]
  have hQT : Q*T.conjTranspose=T.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hTQ
    simpa only [Matrix.conjTranspose_mul,hQstar] using h
  have hQB : Q*B=B := by
    dsimp [B]
    rw [Matrix.mul_smul,←Matrix.mul_assoc,hQT]
  have hBQ : B*Q=B := by
    dsimp [B]
    rw [Matrix.smul_mul,Matrix.mul_assoc,hTQ]
  have hBT : T*B=T := by
    dsimp [B]
    rw [Matrix.mul_smul,←Matrix.mul_assoc,hTT,Matrix.smul_mul,hPT,smul_smul,ha,one_smul]
  have hBB : B*B=B := by
    dsimp [B]
    rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,
      ←Matrix.mul_assoc T T.conjTranspose T,hTT,Matrix.smul_mul,hPT,
      Matrix.mul_smul,smul_smul,smul_smul]
    rw [mul_assoc,ha,mul_one]
  have hBstar : B.conjTranspose=B := by
    simp only [B,a,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,Complex.star_def,Complex.conj_ofReal]
  have htrace : Matrix.trace B=Matrix.trace P := by
    dsimp [B]
    rw [Matrix.trace_smul,Matrix.trace_mul_comm,hTT,Matrix.trace_smul,smul_smul,ha,one_smul]
  change (Q-B).conjTranspose=Q-B ∧ (Q-B)*(Q-B)=Q-B ∧
    (Q-B)*Q=Q-B ∧ T*(Q-B)=0 ∧ Matrix.trace (Q-B)=_
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [Matrix.conjTranspose_sub,hQstar,hBstar]
  · rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hQsq,hQB,hBQ,hBB]
    abel
  · rw [Matrix.sub_mul,hQsq,hBQ]
  · rw [Matrix.mul_sub,hTQ,hBT,sub_self]
  · rw [Matrix.trace_sub,htrace]

/-- A self-adjoint idempotent is positive, and trace zero forces it to
vanish. These are the positivity facts used at the scalar cutoff. -/
theorem mesh_projection_trace (P : Matrix I I ℂ)
    (hstar : P.conjTranspose=P) (hsq : P*P=P) :
    0≤(Matrix.trace P).re ∧ (Matrix.trace P=0 ↔ P=0) := by
  have hpos : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hstar,hsq] at h
  have hz := Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := P)
  rw [hstar,hsq] at hz
  exact ⟨(Complex.nonneg_iff.mp hpos.trace_nonneg).1,hz⟩

end HarmonicArtin.ParabolicIntersections

end OAI
