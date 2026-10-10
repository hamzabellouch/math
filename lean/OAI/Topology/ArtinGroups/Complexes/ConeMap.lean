import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Quivers.TestTransform

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map

variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
  {G : BasedComplex Q (K := K) L} {H : BasedComplex Q (K := K) N}

lemma coneMap_entries (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    ProjectiveEntries Q (f.conePlacement Q) (g.conePlacement Q)
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact b.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact b.entries.2 i j

lemma coneMap_degree (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    MapDegree Q (f.conePlacement Q) (g.conePlacement Q) 0 0
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (a.degree i j).1
      intro he
      apply hc
      dsimp only [conePlacement]
      omega
    · exact (a.degree i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact b.degree i j

noncomputable def coneMap (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H)
    (comm : a.matrix * g.matrix = f.matrix * b.matrix) :
    Map Q (f.cone Q) (g.cone Q) where
  matrix := Matrix.fromBlocks a.matrix 0 0 b.matrix
  entries := coneMap_entries Q f g a b
  degree := coneMap_degree Q f g a b
  commute := by
    change f.coneDifferential Q * _ = _ * g.coneDifferential Q
    unfold coneDifferential
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, neg_zero, a.commute, b.commute, comm]

lemma coconeMap_entries (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    ProjectiveEntries Q (f.coconePlacement Q) (g.coconePlacement Q)
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact b.entries.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact a.entries.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact b.entries.2 i j

lemma coconeMap_degree (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H) :
    MapDegree Q (f.coconePlacement Q) (g.coconePlacement Q) 0 0
      (Matrix.fromBlocks a.matrix 0 0 b.matrix) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact a.degree i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (b.degree i j).1
      intro he
      apply hc
      dsimp only [coconePlacement]
      omega
    · exact (b.degree i j).2

noncomputable def coconeMap (f : Map Q E F) (g : Map Q G H)
    (a : Map Q E G) (b : Map Q F H)
    (comm : a.matrix * g.matrix = f.matrix * b.matrix) :
    Map Q (f.cocone Q) (g.cocone Q) where
  matrix := Matrix.fromBlocks a.matrix 0 0 b.matrix
  entries := coconeMap_entries Q f g a b
  degree := coconeMap_degree Q f g a b
  commute := by
    change f.coconeDifferential Q * _ = _ * g.coconeDifferential Q
    unfold coconeDifferential
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, neg_zero, a.commute, b.commute, comm]

variable [Fintype V] [DecidableEq A]

noncomputable def positiveTwist (f : Map Q E F) (α : V) :
    Map Q (E.positiveTwist Q α) (F.positiveTwist Q α) :=
  coneMap Q (E.evaluation Q α) (F.evaluation Q α) (f.test Q α) f
    (evaluation_natural Q α f.entries)

noncomputable def negativeTwist (f : Map Q E F) (α : V) :
    Map Q (E.negativeTwist Q α) (F.negativeTwist Q α) :=
  coconeMap Q (E.coevaluation Q α) (F.coevaluation Q α) f (f.cotest Q α)
    (coevaluation_natural Q α f.entries).symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.Map

end OAI
