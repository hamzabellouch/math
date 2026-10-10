import OAI.RingTheory.DirectFiniteness.AlgebraicPacking

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
namespace KaplanskyCounterexample.Rectangular
variable {K : Type u_1} {R : Type u_2} {V : Type u_3} {F : Type u_4} {m : Type u_5} [CommRing K] [Ring R] [Algebra K R]
variable [Fintype V] [Fintype F] [Fintype m]

def U (X : Matrix m V K) (P : V → R) : Matrix m V R := fun i v => X i v • P v
def T (X : Matrix m V K) (P : V → R) : Matrix V m R := fun v i => X i v • P v

omit [Fintype m] in
theorem identities (X : Matrix m V K) (P : V → R) (L : F → R)
    (Inc : F → Finset V)
    (hP : ∀ v, P v * P v = P v)
    (hdec : ∀ v, P v = 1 + ∑ f : {f : F // v ∈ Inc f}, (L f - 1))
    (hglobal : X * X.transpose = 1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0) :
    U X P * Matrix.diagonal P = U X P ∧
      Matrix.diagonal P * T X P = T X P ∧ U X P * T X P = 1 := by
  constructor
  · ext i v
    simp [U, Matrix.mul_diagonal, hP]
  constructor
  · ext v i
    simp [T, Matrix.diagonal_mul, hP]
  · ext i j
    change (∑ v, (X i v • P v) * (X j v • P v)) = (1 : Matrix m m R) i j
    simp_rw [smul_mul_smul_comm, hP, hdec, smul_add, Finset.smul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    have hh := congrFun (congrFun hglobal i) j
    change ∑ v, X i v * X j v = (1 : Matrix m m K) i j at hh
    rw [hh]
    have hzero : ∑ v : V, ∑ f : {f : F // v ∈ Inc f},
        (X i v * X j v) • (L f.val - 1) = 0 := by
      have hv (v : V) : (∑ f : {f : F // v ∈ Inc f},
          (X i v * X j v) • (L f.val - 1)) =
          ∑ f : F, if v ∈ Inc f then (X i v * X j v) • (L f - 1) else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype (p := fun f : F => v ∈ Inc f)
          (Finset.univ.filter (fun f : F => v ∈ Inc f)) (by simp)
          (fun f : F => (X i v * X j v) • (L f - 1))).symm
      simp_rw [hv]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro f _
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun v => v ∈ Inc f) = Inc f := by ext; simp
      rw [hf, ← Finset.sum_smul, hlocal, zero_smul]
    rw [hzero, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end KaplanskyCounterexample.Rectangular
end

end OAI
