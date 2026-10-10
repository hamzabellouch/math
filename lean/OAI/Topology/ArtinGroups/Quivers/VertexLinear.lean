import Mathlib
import OAI.Topology.ArtinGroups.Quivers.PathTwoSelf

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*}

def vertexLinear : Q.Zigzag K →ₗ[K] (V → K) where
  toFun := vertex
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def arrowLinear : Q.Zigzag K →ₗ[K] (A → K) where
  toFun := arrow
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vertex_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).vertex = ∑ t ∈ s, (f t).vertex :=
  map_sum (vertexLinear Q) f s

lemma arrow_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).arrow = ∑ t ∈ s, (f t).arrow :=
  map_sum (arrowLinear Q) f s

def TokenMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).vertex = 0 ∧ (f i j).arrow = 0

lemma matrixTwo_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : TokenMatrix Q f) :
    matrixTwo Q f = f := by
  apply Matrix.ext
  intro i j
  exact pathTwo_eq_self Q (hf i j).1 (hf i j).2

lemma tokenMatrix_sub {f g : Matrix I J (Q.Zigzag K)}
    (hf : TokenMatrix Q f) (hg : TokenMatrix Q g) : TokenMatrix Q (f-g) := by
  intro i j
  constructor
  · change (f i j).vertex - (g i j).vertex = 0
    rw [(hf i j).1, (hg i j).1, sub_zero]
  · change (f i j).arrow - (g i j).arrow = 0
    rw [(hf i j).2, (hg i j).2, sub_zero]

lemma tokenMatrix_smul (r : K) {f : Matrix I J (Q.Zigzag K)}
    (hf : TokenMatrix Q f) : TokenMatrix Q (r • f) := by
  intro i j
  constructor
  · change r • (f i j).vertex = 0
    rw [(hf i j).1, smul_zero]
  · change r • (f i j).arrow = 0
    rw [(hf i j).2, smul_zero]

lemma tokenMatrix_matrixTwo_mul [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    TokenMatrix Q (matrixTwo Q f * g) := by
  intro i k
  constructor
  · rw [Matrix.mul_apply, vertex_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [vertex_mul]
    exact MulZeroClass.zero_mul _
  · rw [Matrix.mul_apply, arrow_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [arrow_mul]
    ext a
    change (0 : K) * (g j k).arrow a + 0 * (g j k).vertex (Q.target a) = 0
    simp only [MulZeroClass.zero_mul, add_zero]

lemma tokenMatrix_mul_matrixTwo [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) (g : Matrix J L (Q.Zigzag K)) :
    TokenMatrix Q (f * matrixTwo Q g) := by
  intro i k
  constructor
  · rw [Matrix.mul_apply, vertex_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [vertex_mul]
    exact MulZeroClass.mul_zero _
  · rw [Matrix.mul_apply, arrow_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [arrow_mul]
    ext a
    change (f i j).vertex (Q.source a) * (0 : K) + (f i j).arrow a * 0 = 0
    simp only [MulZeroClass.mul_zero, add_zero]

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma tokenHomDifferential_tokenMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    TokenMatrix Q (tokenHomDifferential Q E F n f) := by
  rw [tokenHomDifferential_apply Q E F hE hF]
  exact tokenMatrix_sub Q (tokenMatrix_matrixTwo_mul Q _ _)
    (tokenMatrix_smul Q _ (tokenMatrix_mul_matrixTwo Q _ _))

lemma homDifferential_tokenMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : TokenMatrix Q f) :
    homDifferential Q E F n f = 0 := by
  rw [← matrixTwo_eq_self Q hf]
  change E.differential * matrixTwo Q f - cochainSign (K := K) n •
    (matrixTwo Q f * F.differential) = 0
  rw [positive_mul_matrixTwo Q hE, matrixTwo_mul_positive Q _ hF, smul_zero, sub_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
