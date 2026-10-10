import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ExtendLayer
import OAI.Topology.ArtinGroups.Quivers.CoefficientMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

def pathTwo : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (0, 0, x.token)
  map_add' _ _ := by
    apply ext
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
    · change (0 : A → K) = 0 + 0
      rw [add_zero]
    · rfl
  map_smul' r x := by
    apply ext
    · change (0 : V → K) = r • 0
      rw [smul_zero]
    · change (0 : A → K) = r • 0
      rw [smul_zero]
    · rfl

lemma path_decomposition (x : Q.Zigzag K) :
    pathZero Q x + pathOne Q x + pathTwo Q x = x := by
  apply ext
  · change x.vertex + 0 + 0 = x.vertex
    simp only [add_zero]
  · change (0 : A → K) + x.arrow + 0 = x.arrow
    simp only [zero_add, add_zero]
  · change (0 : V → K) + 0 + x.token = x.token
    simp only [zero_add]

lemma pathTwo_mul_positive (x : Q.Zigzag K) {y : Q.Zigzag K} (hy : y.vertex = 0) :
    pathTwo Q x * y = 0 := tokenOnly_mul_positive Q rfl rfl hy

lemma positive_mul_pathTwo {x : Q.Zigzag K} (hx : x.vertex = 0) (y : Q.Zigzag K) :
    x * pathTwo Q y = 0 := positive_mul_tokenOnly Q hx rfl rfl

variable {I J L : Type*}

def matrixTwo : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathTwo Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathTwo Q).map_smul' r (f i j)

lemma matrix_decomposition (f : Matrix I J (Q.Zigzag K)) :
    matrixZero Q f + matrixOne Q f + matrixTwo Q f = f := by
  apply Matrix.ext
  intro i j
  exact path_decomposition Q (f i j)

lemma positive_matrix_decomposition {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixOne Q f + matrixTwo Q f = f := by
  have h := matrix_decomposition Q f
  rw [matrixZero_eq_zero Q hf, zero_add] at h
  exact h

lemma matrixTwo_mul_positive [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) {g : Matrix J L (Q.Zigzag K)}
    (hg : PositiveMatrix Q g) : matrixTwo Q f * g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => pathTwo_mul_positive Q _ (hg t j)

lemma positive_mul_matrixTwo [Fintype J]
    {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f)
    (g : Matrix J L (Q.Zigzag K)) : f * matrixTwo Q g = 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun t _ => positive_mul_pathTwo Q (hf i t) _

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def linearHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f := matrixOne Q E.differential * f -
    cochainSign (K := K) n • (f * matrixOne Q F.differential)
  map_add' f g := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' r f := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply]
    rw [smul_comm]

noncomputable def tokenHomDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) :
    Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) :=
  homDifferential Q E F n - linearHomDifferential Q E F n

lemma tokenHomDifferential_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    tokenHomDifferential Q E F n f = matrixTwo Q E.differential * f -
      cochainSign (K := K) n • (f * matrixTwo Q F.differential) := by
  change (E.differential * f - cochainSign (K := K) n • (f * F.differential)) -
    (matrixOne Q E.differential * f - cochainSign (K := K) n • (f * matrixOne Q F.differential)) = _
  conv_lhs =>
    arg 1
    rw [← positive_matrix_decomposition Q hE, ← positive_matrix_decomposition Q hF]
  simp only [Matrix.add_mul, Matrix.mul_add, smul_add]
  abel

lemma tokenHomDifferential_positive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    tokenHomDifferential Q E F n f = 0 := by
  rw [tokenHomDifferential_apply Q E F hE hF,
    matrixTwo_mul_positive Q _ hf, positive_mul_matrixTwo Q hf, smul_zero, sub_zero]

lemma homDifferential_eq_linear_add_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    homDifferential Q E F n f =
      linearHomDifferential Q E F n f + tokenHomDifferential Q E F n f := by
  change homDifferential Q E F n f = linearHomDifferential Q E F n f +
    (homDifferential Q E F n f - linearHomDifferential Q E F n f)
  abel

lemma secondary_kernel_zero [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (n v : ℤ)
    (hd : homDimension Q E F n v = 0)
    {f g : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (hg : g ∈ homSpace Q E F n v)
    (h₀ : CoefficientMatrix Q f) (h₁ : LinearMatrix Q g)
    (hcycle : linearHomDifferential Q E F n f = 0)
    (hboundary : tokenHomDifferential Q E F n f = linearHomDifferential Q E F n g) :
    f = 0 := by
  apply coefficient_eq_zero_of_same_differential Q E F hE hF n v hd hf hg h₀ h₁
  rw [homDifferential_eq_linear_add_token Q E F n f,
    homDifferential_eq_linear_add_token Q E F n g,
    hcycle, zero_add, hboundary,
    tokenHomDifferential_positive Q E F hE hF n (fun i j => (h₁ i j).1), add_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
