import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestIndex
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement
import OAI.Topology.ArtinGroups.Complexes.ConePlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

namespace Map

def coconePlacement (_f : Map Q E F) : I ⊕ J → GeneratorPlacement V
  | .inl i => E.placement i
  | .inr j => ⟨(F.placement j).color, (F.placement j).cochain + 1,
      (F.placement j).internal⟩

noncomputable def coconeDifferential (f : Map Q E F) :
    Matrix (I ⊕ J) (I ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks E.differential f.matrix 0 (-F.differential)

lemma cocone_entries (f : Map Q E F) :
    ProjectiveEntries Q (f.coconePlacement Q) (f.coconePlacement Q)
      (f.coconeDifferential Q) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact E.entries.1 i j
    · exact f.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q F.entries).1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact E.entries.2 i j
    · exact f.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q F.entries).2 i j

lemma cocone_degree (f : Map Q E F) :
    MapDegree Q (f.coconePlacement Q) (f.coconePlacement Q) 1 0
      (f.coconeDifferential Q) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact E.degree i j
  · constructor
    · intro hc
      apply (f.degree i j).1
      intro he
      apply hc
      dsimp only [coconePlacement]
      omega
    · exact (f.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      have hd : (F.placement j).cochain ≠ (F.placement i).cochain + 1 := by
        intro he
        apply hc
        dsimp only [coconePlacement]
        omega
      change -F.differential i j = 0
      rw [(F.degree i j).1 hd, neg_zero]
    · exact homogeneous_neg Q (F.degree i j).2

lemma cocone_square (f : Map Q E F) :
    f.coconeDifferential Q * f.coconeDifferential Q = 0 := by
  unfold coconeDifferential
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.neg_mul, Matrix.mul_neg, E.square_zero, F.square_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, f.commute, add_neg_cancel, neg_zero]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

noncomputable def cocone (f : Map Q E F) : BasedComplex Q (K := K) (I ⊕ J) where
  placement := f.coconePlacement Q
  differential := f.coconeDifferential Q
  entries := f.cocone_entries Q
  degree := f.cocone_degree Q
  square_zero := f.cocone_square Q

end Map

variable [Fintype V] [DecidableEq A]

noncomputable def positiveTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α ⊕ I) :=
  (E.evaluation Q α).cone Q

noncomputable def negativeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (I ⊕ TestIndex Q E.placement α) :=
  (E.coevaluation Q α).cocone Q

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
