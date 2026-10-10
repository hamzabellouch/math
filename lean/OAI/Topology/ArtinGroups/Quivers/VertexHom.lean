import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def vertexHom (v : V) : Q.Zigzag K →+* K where
  toFun x := x.vertex v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def vertexId (v : V) : Q.Zigzag K := (Pi.single v 1, 0, 0)

omit [Fintype A] in
@[simp] theorem vertex_vertexId (v : V) :
    (vertexId Q v).vertex = Pi.single v (1 : K) := rfl
omit [Fintype A] in
@[simp] theorem arrow_vertexId (v : V) :
    (vertexId Q (K := K) v).arrow = 0 := rfl
omit [Fintype A] in
@[simp] theorem token_vertexId (v : V) :
    (vertexId Q (K := K) v).token = 0 := rfl

@[simp] theorem vertexId_mul_self (v : V) :
    vertexId Q (K := K) v * vertexId Q v = vertexId Q v := by
  apply Zigzag.ext
  · ext w
    by_cases h : w = v <;> simp [h]
  · ext a
    simp [arrow_mul, leftScale, rightScale]
  · ext w
    simp [token_mul]

variable {I J L N : Type*} [Fintype I] [Fintype J] [Fintype L]

def PositiveMatrix (M : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (M i j).vertex = 0

omit [Fintype I] [Fintype J] in
lemma positiveMatrix_add {M N : Matrix I J (Q.Zigzag K)}
    (hM : PositiveMatrix Q M) (hN : PositiveMatrix Q N) :
    PositiveMatrix Q (M + N) := by
  intro i j
  simp [hM i j, hN i j]

omit [Fintype I] [Fintype L] in
lemma positiveMatrix_mul_left (M : Matrix I J (Q.Zigzag K))
    {N : Matrix J L (Q.Zigzag K)} (hN : PositiveMatrix Q N) :
    PositiveMatrix Q (M * N) := by
  intro i l
  funext v
  change (vertexHom Q (K := K) v) ((M * N) i l) = 0
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro j _
  change (M i j).vertex v * (N j l).vertex v = 0
  simp [hN j l]

omit [Fintype I] [Fintype L] in
lemma positiveMatrix_mul_right {M : Matrix I J (Q.Zigzag K)}
    (hM : PositiveMatrix Q M) (N : Matrix J L (Q.Zigzag K)) :
    PositiveMatrix Q (M * N) := by
  intro i l
  funext v
  change (vertexHom Q (K := K) v) ((M * N) i l) = 0
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_eq_zero
  intro j _
  change (M i j).vertex v * (N j l).vertex v = 0
  simp [hM i j]

omit [Fintype I] in

lemma positiveMatrix_triple
    (M : Matrix I J (Q.Zigzag K)) (N' : Matrix J L (Q.Zigzag K))
    (P : Matrix L N (Q.Zigzag K)) (hM : PositiveMatrix Q M)
    (hN : PositiveMatrix Q N') (hP : PositiveMatrix Q P) :
    M * N' * P = 0 := by
  apply Matrix.ext
  intro i n
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro j _
  exact positive_triple_mul Q (M i j) (N' j l) (P l n) (hM i j) (hN j l) (hP l n)

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
