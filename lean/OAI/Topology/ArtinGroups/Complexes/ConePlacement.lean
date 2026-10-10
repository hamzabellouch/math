import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

namespace Map

def conePlacement (_f : Map Q E F) : I ⊕ J → GeneratorPlacement V
  | .inl i => ⟨(E.placement i).color, (E.placement i).cochain - 1,
      (E.placement i).internal⟩
  | .inr j => F.placement j

noncomputable def coneDifferential (f : Map Q E F) : Matrix (I ⊕ J) (I ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks (-E.differential) f.matrix 0 F.differential

lemma cone_entries (f : Map Q E F) :
    ProjectiveEntries Q (f.conePlacement Q) (f.conePlacement Q) (f.coneDifferential Q) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q E.entries).1 i j
    · exact f.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact F.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q E.entries).2 i j
    · exact f.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact F.entries.2 i j

lemma cone_degree (f : Map Q E F) :
    MapDegree Q (f.conePlacement Q) (f.conePlacement Q) 1 0 (f.coneDifferential Q) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      have hd : (E.placement j).cochain ≠ (E.placement i).cochain + 1 := by
        intro he
        apply hc
        dsimp only [conePlacement]
        omega
      change -E.differential i j = 0
      rw [(E.degree i j).1 hd, neg_zero]
    · exact homogeneous_neg Q (E.degree i j).2
  · constructor
    · intro hc
      apply (f.degree i j).1
      intro he
      apply hc
      dsimp only [conePlacement]
      omega
    · exact (f.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact F.degree i j

lemma cone_square (f : Map Q E F) : f.coneDifferential Q * f.coneDifferential Q = 0 := by
  unfold coneDifferential
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, E.square_zero, F.square_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, f.commute, neg_add_cancel, neg_zero]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

noncomputable def cone (f : Map Q E F) : BasedComplex Q (K := K) (I ⊕ J) where
  placement := f.conePlacement Q
  differential := f.coneDifferential Q
  entries := f.cone_entries Q
  degree := f.cone_degree Q
  square_zero := f.cone_square Q

end Map
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
