import Mathlib
import OAI.RepresentationTheory.Saxl.Main

namespace OAI

/-! Odd Path. -/

section

noncomputable section
namespace Saxl.Band

def basisCoordinates : Mat →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun X := ![(X 0 0 + X 1 1)/2, (X 0 0 - X 1 1)/2,
    (X 0 1 + X 1 0)/2, (X 0 1 - X 1 0)/2]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp <;> ring

def matrixBasisEquiv : (Fin 4 → ℂ) ≃ₗ[ℂ] Mat where
  toFun c := ∑ i : Fin 4, c i • basis i.val
  invFun := basisCoordinates
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp [smul_smul, Finset.smul_sum]
  left_inv c := by
    ext i
    fin_cases i <;>
      simp [basisCoordinates, Fin.sum_univ_succ, basis] <;> ring
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisCoordinates, Fin.sum_univ_succ, basis] <;> ring

def conjugationEquiv : Mat ≃ₗ[ℂ] Mat where
  toLinearMap := conjugation
  invFun X := Qinv * X * Q
  left_inv X := by
    change Qinv * (Q * X * Qinv) * Q = X
    simp only [mul_assoc, Qinv_mul_Q, mul_one]
    rw [← mul_assoc Qinv Q X, Qinv_mul_Q, one_mul]
  right_inv X := by
    change Q * (Qinv * X * Q) * Qinv = X
    simp only [mul_assoc, Q_mul_Qinv, mul_one]
    rw [← mul_assoc Q Qinv X, Q_mul_Qinv, one_mul]

def pathBasis : Module.Basis (Fin 4) ℂ Mat :=
  (Pi.basisFun ℂ (Fin 4)).map (matrixBasisEquiv.trans conjugationEquiv)

lemma pathBasis_apply (i : Fin 4) : pathBasis i = conjugation (basis i.val) := by
  simp [pathBasis, matrixBasisEquiv, Pi.basisFun_apply,
    Pi.single_apply, conjugationEquiv]

end Saxl.Band

namespace Saxl.Columns

def dualBlockWord (rs : List ℕ) (N : ℕ → Band.Mat) : WordSpace rs.sum 4 :=
  ∑ π : Perms rs, sg π • Path.pureWord
    (fun q => N (row (perm π (enumerate rs q))))

lemma chainFunctional_dualBlockWord (rs : List ℕ) (N : ℕ → Band.Mat) (p : ℕ) :
    Path.chainFunctional rs.sum p (dualBlockWord rs N) = segments p rs N := by
  rw [dualBlockWord, map_sum]
  simp_rw [map_smul, Path.chainFunctional_pure]
  exact sum_chain rs p N

theorem odd_path_ordered_contraction (r : ℕ) (rs : List ℕ)
    (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*r+1) :
    dotProduct
      (fun w : Fin (2*r+1) → Fin 4 =>
        dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
          (w ∘ Fin.cast hn))
      (Path.bandWord r) ≠ 0 := by
  have h := Band.conjugation_blocks_ne_zero rs hrs
  rw [← Band.segments_conjugation rs 1,
    ← chainFunctional_dualBlockWord rs (fun i => Band.conjugation (Band.basis i)) 1] at h
  have hc : Path.chainFunctional (2*r+1) 1
      (fun w => dualBlockWord rs (fun i => Band.conjugation (Band.basis i))
        (w ∘ Fin.cast hn)) =
      Path.chainFunctional rs.sum 1
        (dualBlockWord rs (fun i => Band.conjugation (Band.basis i))) := by
    have aux : ∀ (m n : ℕ) (h : m = n) (x : WordSpace m 4),
        Path.chainFunctional n 1 (fun w => x (w ∘ Fin.cast h)) =
          Path.chainFunctional m 1 x := by
      intro m n h x
      subst n
      rfl
    exact aux _ _ hn _
  rw [← hc, Path.chainFunctional_endpoint] at h
  exact (mul_ne_zero_iff.mp h).2

end Saxl.Columns
end
end

end OAI
