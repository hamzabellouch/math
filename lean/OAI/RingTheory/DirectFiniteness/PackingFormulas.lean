import OAI.RingTheory.DirectFiniteness.AlgebraicCriterion

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.AlgebraicPacking
variable {R : Type u_1} {m : Type u_2} {t : Type u_3} [Ring R] [Fintype m] [Fintype t]

theorem prescribed_packing_products (U : Matrix m t R) (T : Matrix t m R)
    (p q u uInv : t → R) (slot : t → m) (e : R)
    (he : e * e = e) (hc : ∀ x : R, Commute e x)
    (hp : ∀ v, p v * p v = p v)
    (hUP : U * Matrix.diagonal p = U) (hPT : Matrix.diagonal p * T = T)
    (hUT : U * T = 1)
    (hlu : ∀ v, uInv v * u v = 1)
    (hconj : ∀ v, u v * (e * p v) * uInv v = e * q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → q v * q w = 0)
    (hdefect : Matrix.diagonal (fun _ : t => e) * (T * U - Matrix.diagonal p) ≠ 0) :
    let a := aMat U (Jpack slot uInv (fun v => e*p v)) (Matrix.diagonal (fun _ => e))
    let b := bMat (Cpack slot u (fun v => e*p v)) T (Matrix.diagonal (fun _ => e))
    a*b=1 ∧ b*a≠1 := by
  let D : t → R := fun v => e * p v
  let C := Cpack slot u D
  let J := Jpack slot uInv D
  let E : Matrix m m R := Matrix.diagonal (fun _ => e)
  let F : Matrix t t R := Matrix.diagonal (fun _ => e)
  have hD (v : t) : D v * D v = D v := by
    dsimp [D]
    calc
      e * p v * (e * p v) = e * (e * p v) * p v := by
        rw [mul_assoc, ← mul_assoc (p v), (hc (p v)).eq.symm]; simp only [mul_assoc]
      _ = e * p v := by rw [← mul_assoc e e, he, mul_assoc, hp]
  have horth' (v w : t) (hne : v ≠ w) (hs : slot v = slot w) :
      (e * q v) * (e * q w) = 0 := by
    calc
      e * q v * (e * q w) = (e * e) * (q v * q w) := by
        rw [mul_assoc, ← mul_assoc (q v), (hc (q v)).eq.symm]; simp only [mul_assoc]
      _ = 0 := by rw [horth v w hne hs, mul_zero]
  have hJC : J * C = F * Matrix.diagonal p := by
    rw [show F * Matrix.diagonal p = Matrix.diagonal D by
      simp [F, D, Matrix.diagonal_mul_diagonal]]
    exact Jpack_mul_Cpack slot u uInv D (fun v => e * q v) hlu hD hconj horth'
  have hEE : E * E = E := by simp [E, Matrix.diagonal_mul_diagonal, he]
  have hFF : F * F = F := by simp [F, Matrix.diagonal_mul_diagonal, he]
  have hEU : E * U = U * F := by
    ext i v
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (U i v)).eq
  have hFT : F * T = T * E := by
    ext v i
    simpa [E, F, Matrix.diagonal_mul, Matrix.mul_diagonal] using (hc (T v i)).eq
  have hC (i : m) (v : t) : e * C i v = C i v := by
    dsimp [C, Cpack, D]
    split_ifs
    · rw [← mul_assoc, (hc (u v)).eq, mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJ (v : t) (i : m) : e * J v i = J v i := by
    dsimp [J, Jpack, D]
    split_ifs
    · rw [← mul_assoc, ← mul_assoc e e, he]
    · exact mul_zero e
  have hJE : J * E = J := by
    ext v i
    simp only [E, Matrix.mul_diagonal]
    rw [← (hc (J v i)).eq, hJ]
  have hEC : E * C = C := by ext i v; simpa [E, Matrix.diagonal_mul] using hC i v
  have hCF : C * F = C := by
    ext i v
    simp only [F, Matrix.mul_diagonal]
    rw [← (hc (C i v)).eq, hC]
  have hFJ : F * J = J := by ext v i; simpa [F, Matrix.diagonal_mul] using hJ v i
  obtain ⟨hab, hdelta⟩ := packing_identities U C T J (Matrix.diagonal p) F E
    hUP hPT hUT hJC hEE hFF hEU hFT hJE hEC hCF hFJ
  refine ⟨hab, ?_⟩
  intro hba
  apply hdefect
  rw [hba, sub_self, Matrix.mul_zero, Matrix.zero_mul] at hdelta
  exact hdelta.symm

end KaplanskyCounterexample.AlgebraicPacking
end

end OAI
