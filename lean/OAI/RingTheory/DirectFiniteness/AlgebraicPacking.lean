import OAI.RingTheory.DirectFiniteness.CharacterTwist

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.AlgebraicPacking

variable {R : Type u_1} {m : Type u_2} {t : Type u_3} [Ring R] [Fintype m] [Fintype t]

def aMat (U : Matrix m t R) (J : Matrix t m R) (E : Matrix m m R) : Matrix m m R :=
  U * J + (1 - E)

def bMat (C : Matrix m t R) (T : Matrix t m R) (E : Matrix m m R) : Matrix m m R :=
  C * T + (1 - E)

theorem packing_identities
    (U C : Matrix m t R) (T J : Matrix t m R) (P F : Matrix t t R)
    (E : Matrix m m R)
    (hUP : U * P = U) (hPT : P * T = T) (hUT : U * T = 1)
    (hJC : J * C = F * P) (hEE : E * E = E) (hFF : F * F = F)
    (hEU : E * U = U * F) (hFT : F * T = T * E)
    (hJE : J * E = J) (hEC : E * C = C)
    (hCF : C * F = C) (hFJ : F * J = J) :
    aMat U J E * bMat C T E = 1 ∧
      J * (bMat C T E * aMat U J E - 1) * C = F * (T * U - P) := by
  have hUJCT : U * J * (C * T) = E := by
    calc
      U * J * (C * T) = U * (J * C) * T := by simp only [Matrix.mul_assoc]
      _ = U * (F * P) * T := by rw [hJC]
      _ = E * (U * (P * T)) := by rw [← Matrix.mul_assoc U, ← hEU]; simp only [Matrix.mul_assoc]
      _ = E := by rw [hPT, hUT, Matrix.mul_one]
  have hUJE : (U * J) * E = U * J := by rw [Matrix.mul_assoc, hJE]
  have hECT : E * (C * T) = C * T := by rw [← Matrix.mul_assoc, hEC]
  have hproj : (1 - E) * (1 - E) = 1 - E := by
    noncomm_ring [hEE]
  constructor
  · unfold aMat bMat
    rw [mul_add, add_mul, add_mul, hUJCT, mul_sub, Matrix.mul_one,
      hUJE, sub_self, sub_mul, Matrix.one_mul, hECT, sub_self, hproj]
    abel
  · have hCTE : C * T * E = C * T := by
      rw [Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hCF]
    have hEUJ : E * (U * J) = U * J := by
      rw [← Matrix.mul_assoc, hEU, Matrix.mul_assoc, hFJ]
    have hdelta : bMat C T E * aMat U J E - 1 = C * T * (U * J) - E := by
      unfold aMat bMat
      rw [mul_add, add_mul, add_mul, mul_sub, Matrix.mul_one, hCTE,
        sub_self, sub_mul, Matrix.one_mul, hEUJ, sub_self, hproj]
      abel
    have hsandwich : J * (C * T * (U * J)) * C = F * (T * U) := by
      calc
        J * (C * T * (U * J)) * C = (J * C) * T * U * (J * C) := by
          simp only [Matrix.mul_assoc]
        _ = (F * P) * T * U * (F * P) := by rw [hJC]
        _ = F * T * (U * F) * P := by
          rw [Matrix.mul_assoc F P T, hPT]
          simp only [Matrix.mul_assoc]
        _ = F * (T * E) * (U * P) := by
          rw [← hEU]
          simp only [Matrix.mul_assoc]
        _ = F * (F * T) * U := by rw [hUP, ← hFT]
        _ = F * (T * U) := by
          rw [← Matrix.mul_assoc F F T, hFF, Matrix.mul_assoc]
    rw [hdelta, Matrix.mul_sub, Matrix.sub_mul, hsandwich, hJE, hJC, Matrix.mul_sub]

/-- The rank defect used after specialization to the subgroup algebra. -/
theorem transpose_mul_ne_one {K : Type u_4} {m : Type u_5} {t : Type u_6} [Field K] [Fintype m] [Fintype t]
    (X : Matrix m t K) (hlt : Fintype.card m < Fintype.card t) :
    X.transpose * X ≠ 1 := by
  intro heq
  have h := (Matrix.rank_mul_le_right X.transpose X).trans (Matrix.rank_le_card_height X)
  rw [heq, Matrix.rank_one] at h
  omega

def Cpack (slot : t → m) (u D : t → R) : Matrix m t R :=
  fun i v => if slot v = i then u v * D v else 0

def Jpack (slot : t → m) (uInv D : t → R) : Matrix t m R :=
  fun v i => if slot v = i then D v * uInv v else 0

omit [Fintype t] in
lemma Jpack_mul_Cpack (slot : t → m) (u uInv D Q : t → R)
    (hlu : ∀ v, uInv v * u v = 1)
    (hD : ∀ v, D v * D v = D v)
    (hconj : ∀ v, u v * D v * uInv v = Q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → Q v * Q w = 0) :
    Jpack slot uInv D * Cpack slot u D = Matrix.diagonal D := by
  have hleft (v : t) : D v * uInv v = uInv v * Q v := by
    rw [← hconj, ← mul_assoc, ← mul_assoc, hlu, one_mul]
  have hright (v : t) : u v * D v = Q v * u v := by
    rw [← hconj, mul_assoc (u v * D v), hlu, mul_one]
  ext v w
  rw [Matrix.mul_apply]
  by_cases hvw : v = w
  · subst w
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single (slot v)]
    · simp only [Jpack, Cpack, ite_true]
      rw [mul_assoc, ← mul_assoc (uInv v), hlu, one_mul, hD]
    · intro i _ hi
      simp [Jpack, Cpack, Ne.symm hi]
    · simp
  · rw [Matrix.diagonal_apply_ne _ hvw]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hvi : slot v = i <;> by_cases hwi : slot w = i <;>
      simp only [Jpack, Cpack, hvi, hwi, ite_true, ite_false, mul_zero, zero_mul]
    rw [hleft, hright, mul_assoc, ← mul_assoc (Q v), horth v w hvw (hvi.trans hwi.symm),
      zero_mul, mul_zero]

theorem square_of_projections (U : Matrix m t R) (T : Matrix t m R)
    (p q u uInv : t → R) (slot : t → m) (e : R)
    (he : e * e = e) (hc : ∀ x : R, Commute e x)
    (hp : ∀ v, p v * p v = p v)
    (hUP : U * Matrix.diagonal p = U) (hPT : Matrix.diagonal p * T = T)
    (hUT : U * T = 1)
    (hlu : ∀ v, uInv v * u v = 1)
    (hconj : ∀ v, u v * (e * p v) * uInv v = e * q v)
    (horth : ∀ v w, v ≠ w → slot v = slot w → q v * q w = 0)
    (hdefect : Matrix.diagonal (fun _ : t => e) * (T * U - Matrix.diagonal p) ≠ 0) :
    ∃ a b : Matrix m m R, a * b = 1 ∧ b * a ≠ 1 := by
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
  refine ⟨aMat U J E, bMat C T E, hab, ?_⟩
  intro hba
  apply hdefect
  rw [hba, sub_self, Matrix.mul_zero, Matrix.zero_mul] at hdelta
  exact hdelta.symm

end KaplanskyCounterexample.AlgebraicPacking

end

end OAI
