import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot
import OAI.Topology.ArtinGroups.Quivers.TestIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V B K T R : Type*} (Q : ReversibleQuiver V B) [Field K]
  [Fintype B] [DecidableEq V]
lemma scalarCornerMatrix_degree (α : V) (p : T → GeneratorPlacement V)
    (q : R → GeneratorPlacement V) (M : Matrix T R K) (n v : ℤ)
    (hc : ∀ i j, M i j ≠ 0 → (q j).cochain = (p i).cochain+n)
    (hi : ∀ i j, M i j ≠ 0 → (q j).internal = (p i).internal+v) :
    MapDegree Q p q n v (scalarCornerMatrix Q α M) := by
  intro i j
  constructor
  · intro h
    have hz : M i j=0 := by
      by_contra hn
      exact h (hc i j hn)
    change M i j • vertexId Q α = 0
    rw [hz,zero_smul]
  · by_cases hz : M i j=0
    · change Homogeneous Q _ (M i j • vertexId Q α)
      rw [hz,zero_smul]
      exact homogeneous_zero Q _
    · have he : v+(p i).internal-(q j).internal=0 := by rw [hi i j hz]; omega
      rw [he]
      exact homogeneous_smul Q (homogeneous_vertexId Q α) _

lemma scalarCornerMatrix_identity [DecidableEq T] (α : V)
    (p : T → GeneratorPlacement V) (hp : ∀ i, (p i).color=α) :
    scalarCornerMatrix Q α (1 : Matrix T T K) = projectiveIdentity Q p := by
  apply Matrix.ext
  intro i j
  by_cases h : i=j
  · subst j
    simp only [scalarCornerMatrix,Matrix.one_apply_eq,one_smul,projectiveIdentity,
      Matrix.diagonal_apply,ite_true,hp]
  · simp only [scalarCornerMatrix,Matrix.one_apply_ne h,zero_smul,projectiveIdentity,
      Matrix.diagonal_apply,ite_eq_right h]
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
