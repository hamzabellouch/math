import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Complexes.ConeMap
import OAI.Topology.ArtinGroups.Quivers.TestTransform

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J]

noncomputable def positiveTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V)
    (h : Matrix I I (Q.Zigzag K)) :=
  Matrix.fromBlocks (-testTransform Q E.placement E.placement α h) 0 0 h

noncomputable def negativeTwistHomotopy (E : BasedComplex Q (K := K) I) (α : V)
    (h : Matrix I I (Q.Zigzag K)) :=
  Matrix.fromBlocks h 0 0 (-testTransform Q E.placement E.placement α h)

lemma positiveTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    ProjectiveEntries Q (E.positiveTwist Q α).placement (E.positiveTwist Q α).placement
      (positiveTwistHomotopy Q E α h) := by
  have ht : ProjectiveEntries Q (testPlacement Q E.placement α)
      (testPlacement Q E.placement α) (testTransform Q E.placement E.placement α h) :=
    scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q ht).1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact hh.1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact (projectiveEntries_neg Q ht).2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact hh.2 i j

lemma negativeTwistHomotopy_entries (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    ProjectiveEntries Q (E.negativeTwist Q α).placement (E.negativeTwist Q α).placement
      (negativeTwistHomotopy Q E α h) := by
  have ht : ProjectiveEntries Q (cotestPlacement Q E.placement α)
      (cotestPlacement Q E.placement α) (testTransform Q E.placement E.placement α h) :=
    scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hh.1 i j
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _
    · exact (projectiveEntries_neg Q ht).1 i j
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hh.2 i j
    · exact MulZeroClass.zero_mul _
    · exact MulZeroClass.zero_mul _
    · exact (projectiveEntries_neg Q ht).2 i j

lemma positiveTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : MapDegree Q E.placement E.placement (-1) 0 h) :
    MapDegree Q (E.positiveTwist Q α).placement (E.positiveTwist Q α).placement (-1) 0
      (positiveTwistHomotopy Q E α h) := by
  have ht := mapDegree_neg Q (testMatrix_degree Q α hh)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (testPlacement Q E.placement α j).cochain - 1 =
        (testPlacement Q E.placement α i).cochain - 1 + -1
      omega
    · exact (ht i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact hh i j

lemma negativeTwistHomotopy_degree (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : MapDegree Q E.placement E.placement (-1) 0 h) :
    MapDegree Q (E.negativeTwist Q α).placement (E.negativeTwist Q α).placement (-1) 0
      (negativeTwistHomotopy Q E α h) := by
  have ht := mapDegree_neg Q (cotestMatrix_degree Q α hh)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hh i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (cotestPlacement Q E.placement α j).cochain + 1 =
        (cotestPlacement Q E.placement α i).cochain + 1 + -1
      omega
    · exact (ht i j).2

lemma positiveTwistHomotopy_boundary (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    (E.positiveTwist Q α).differential * positiveTwistHomotopy Q E α h +
      positiveTwistHomotopy Q E α h * (E.positiveTwist Q α).differential =
    Matrix.fromBlocks
      (testTransform Q E.placement E.placement α (E.differential * h + h * E.differential))
      0 0 (E.differential * h + h * E.differential) := by
  change Matrix.fromBlocks (-testTransform Q _ _ α E.differential)
      (evaluationMatrix Q E.placement α) 0 E.differential * _ +
    _ * Matrix.fromBlocks (-testTransform Q _ _ α E.differential)
      (evaluationMatrix Q E.placement α) 0 E.differential = _
  unfold positiveTwistHomotopy
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, neg_zero]
  rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hh,
    evaluation_natural Q α hh, add_neg_cancel, testTransform_add]

lemma negativeTwistHomotopy_boundary (E : BasedComplex Q (K := K) I) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h) :
    (E.negativeTwist Q α).differential * negativeTwistHomotopy Q E α h +
      negativeTwistHomotopy Q E α h * (E.negativeTwist Q α).differential =
    Matrix.fromBlocks (E.differential * h + h * E.differential) 0 0
      (testTransform Q E.placement E.placement α (E.differential * h + h * E.differential)) := by
  change Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α) 0
      (-testTransform Q _ _ α E.differential) * _ +
    _ * Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α) 0
      (-testTransform Q _ _ α E.differential) = _
  unfold negativeTwistHomotopy
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, neg_zero]
  rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hh,
    coevaluation_natural Q α hh, neg_add_cancel, testTransform_add]

lemma positiveTwist_identity [DecidableEq I] (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (E.positiveTwist Q α).placement =
      Matrix.fromBlocks (testTransform Q E.placement E.placement α
        (projectiveIdentity Q E.placement)) 0 0 (projectiveIdentity Q E.placement) := by
  rw [testTransform_identity]
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

lemma negativeTwist_identity [DecidableEq I] (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (E.negativeTwist Q α).placement =
      Matrix.fromBlocks (projectiveIdentity Q E.placement) 0 0
        (testTransform Q E.placement E.placement α (projectiveIdentity Q E.placement)) := by
  rw [testTransform_identity]
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

lemma positiveTwist_homotopy_equation [DecidableEq I]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.positiveTwist Q α).matrix * (g.positiveTwist Q α).matrix =
      projectiveIdentity Q (E.positiveTwist Q α).placement +
      ((E.positiveTwist Q α).differential * positiveTwistHomotopy Q E α h +
        positiveTwistHomotopy Q E α h * (E.positiveTwist Q α).differential) := by
  rw [positiveTwistHomotopy_boundary Q E α hh, positiveTwist_identity,
    Matrix.fromBlocks_add]
  change Matrix.fromBlocks (testTransform Q _ _ α f.matrix) 0 0 f.matrix *
    Matrix.fromBlocks (testTransform Q _ _ α g.matrix) 0 0 g.matrix = _
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [testTransform_mul Q α _ f.entries, he, testTransform_add]

lemma negativeTwist_homotopy_equation [DecidableEq I]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (g : Map Q F E) (α : V)
    {h : Matrix I I (Q.Zigzag K)} (hh : ProjectiveEntries Q E.placement E.placement h)
    (he : f.matrix * g.matrix = projectiveIdentity Q E.placement +
      (E.differential * h + h * E.differential)) :
    (f.negativeTwist Q α).matrix * (g.negativeTwist Q α).matrix =
      projectiveIdentity Q (E.negativeTwist Q α).placement +
      ((E.negativeTwist Q α).differential * negativeTwistHomotopy Q E α h +
        negativeTwistHomotopy Q E α h * (E.negativeTwist Q α).differential) := by
  rw [negativeTwistHomotopy_boundary Q E α hh, negativeTwist_identity,
    Matrix.fromBlocks_add]
  change Matrix.fromBlocks f.matrix 0 0 (testTransform Q _ _ α f.matrix) *
    Matrix.fromBlocks g.matrix 0 0 (testTransform Q _ _ α g.matrix) = _
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [testTransform_mul Q α _ f.entries, he, testTransform_add]

namespace HomotopyEquivalence

variable [DecidableEq I] [DecidableEq J]

noncomputable def positiveTwist {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (F.positiveTwist Q α) where
  forward := e.forward.positiveTwist Q α
  backward := e.backward.positiveTwist Q α
  sourceHomotopy := positiveTwistHomotopy Q E α e.sourceHomotopy
  targetHomotopy := positiveTwistHomotopy Q F α e.targetHomotopy
  sourceEntries := positiveTwistHomotopy_entries Q E α e.sourceEntries
  targetEntries := positiveTwistHomotopy_entries Q F α e.targetEntries
  sourceDegree := positiveTwistHomotopy_degree Q E α e.sourceDegree
  targetDegree := positiveTwistHomotopy_degree Q F α e.targetDegree
  sourceEquation := positiveTwist_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := positiveTwist_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

noncomputable def negativeTwist {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (e : HomotopyEquivalence Q E F) (α : V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (F.negativeTwist Q α) where
  forward := e.forward.negativeTwist Q α
  backward := e.backward.negativeTwist Q α
  sourceHomotopy := negativeTwistHomotopy Q E α e.sourceHomotopy
  targetHomotopy := negativeTwistHomotopy Q F α e.targetHomotopy
  sourceEntries := negativeTwistHomotopy_entries Q E α e.sourceEntries
  targetEntries := negativeTwistHomotopy_entries Q F α e.targetEntries
  sourceDegree := negativeTwistHomotopy_degree Q E α e.sourceDegree
  targetDegree := negativeTwistHomotopy_degree Q F α e.targetDegree
  sourceEquation := negativeTwist_homotopy_equation Q e.forward e.backward α
    e.sourceEntries e.sourceEquation
  targetEquation := negativeTwist_homotopy_equation Q e.backward e.forward α
    e.targetEntries e.targetEquation

end HomotopyEquivalence
end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
