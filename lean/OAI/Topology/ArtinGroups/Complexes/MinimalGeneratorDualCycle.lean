import Mathlib
import OAI.Topology.ArtinGroups.Quivers.VertexLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem minimal_generator_dual_cycle
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) (j : J) :
    ∃ x : I → K, x ≠ 0 ∧
      (∀ i, E.placement i ≠ F.placement j → x i = 0) ∧
      ∀ k, ∑ i, (E.differential k i).vertex (F.placement j).color * x i = 0 := by
  have hf0 i k w : (F.differential i k).vertex w = 0 := congrFun (hF i k) w
  let x : I → K := fun i => (e.forward.matrix i j).vertex (F.placement j).color
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx
    have he := congrArg (fun M : Matrix J J (Q.Zigzag K) =>
      (M j j).vertex (F.placement j).color) e.targetEquation
    have hz i : (e.forward.matrix i j).vertex (F.placement j).color = 0 :=
      congrFun hx i
    simp only [Matrix.mul_apply, Matrix.add_apply, vertex_add, Pi.add_apply, vertex_sum,
      Finset.sum_apply, vertex_mul, Pi.mul_apply, hf0, hz,
      MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero,
      add_zero] at he
    simp [projectiveIdentity] at he
  · intro i hi
    by_contra hn
    exact hi ((reduction_support Q e.forward.entries e.forward.degree i j
      (F.placement j).color hn).1)
  · intro k
    have he := congrArg (fun M : Matrix I J (Q.Zigzag K) =>
      (M k j).vertex (F.placement j).color) e.forward.commute
    simpa only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      Pi.mul_apply, hf0, Pi.zero_apply, MulZeroClass.mul_zero,
      Finset.sum_const_zero] using he

theorem minimal_generator_cycle
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) (j : J) :
    ∃ x : I → K, x ≠ 0 ∧
      (∀ i, E.placement i ≠ F.placement j → x i = 0) ∧
      ∀ k, ∑ i, x i * (E.differential i k).vertex (F.placement j).color = 0 := by
  have hf0 i k w : (F.differential i k).vertex w = 0 := congrFun (hF i k) w
  let x : I → K := fun i => (e.backward.matrix j i).vertex (F.placement j).color
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx
    have he := congrArg (fun M : Matrix J J (Q.Zigzag K) =>
      (M j j).vertex (F.placement j).color) e.targetEquation
    have hz i : (e.backward.matrix j i).vertex (F.placement j).color = 0 :=
      congrFun hx i
    simp only [Matrix.mul_apply, Matrix.add_apply, vertex_add, Pi.add_apply, vertex_sum,
      Finset.sum_apply, vertex_mul, Pi.mul_apply, hf0, hz,
      MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero,
      add_zero] at he
    simp [projectiveIdentity] at he
  · intro i hi
    by_contra hn
    exact hi ((reduction_support Q e.backward.entries e.backward.degree j i
      (F.placement j).color hn).1.symm)
  · intro k
    have he := congrArg (fun M : Matrix J I (Q.Zigzag K) =>
      (M j k).vertex (F.placement j).color) e.backward.commute
    simpa only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      Pi.mul_apply, hf0, MulZeroClass.zero_mul, Finset.sum_const_zero] using he.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
