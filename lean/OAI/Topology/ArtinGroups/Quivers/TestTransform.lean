import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def testTransform (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M : Matrix I J (Q.Zigzag K)) :
    Matrix (TestIndex Q p α) (TestIndex Q q α) (Q.Zigzag K) :=
  scalarCornerMatrix Q α (testMatrix Q p q α M)

lemma testTransform_mul [Fintype J] {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {r : L → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (N : Matrix J L (Q.Zigzag K))
    (hM : ProjectiveEntries Q p q M) :
    testTransform Q p q α M * testTransform Q q r α N =
      testTransform Q p r α (M * N) := by
  unfold testTransform
  rw [scalarCornerMatrix_mul, testMatrix_mul Q α N hM]

omit [DecidableEq A] in
lemma testTransform_zero (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) :
    testTransform Q p q α (0 : Matrix I J (Q.Zigzag K)) = 0 := by
  unfold testTransform
  rw [testMatrix_zero, scalarCornerMatrix_zero]

omit [DecidableEq A] in
lemma testTransform_add (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M N : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (M + N) = testTransform Q p q α M +
      testTransform Q p q α N := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.add_apply,
    _root_.mul_add, coordinates_add, add_smul]

omit [DecidableEq A] in
lemma testTransform_neg (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (α : V) (M : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (-M) = -testTransform Q p q α M := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.neg_apply,
    _root_.mul_neg, map_neg, Pi.neg_apply, neg_smul]

lemma testTransform_identity [DecidableEq I] (p : I → GeneratorPlacement V) (α : V) :
    testTransform Q p p α (projectiveIdentity Q p (K := K)) =
      projectiveIdentity Q (testPlacement Q p α) := by
  classical
  apply Matrix.ext
  intro u v
  change pathCoordinates Q (pathBasis Q u.2.val *
    (if u.1 = v.1 then vertexId Q (p u.1).color else 0)) v.2.val • vertexId Q α =
    if u = v then vertexId Q α else 0
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, u⟩
    rcases v with ⟨j, v⟩
    dsimp only at hi
    subst j
    dsimp only
    simp only [ite_true, cornerPath_right, pathBasis_coordinates]
    by_cases hp : u = v
    · subst v
      simp
    · have hv : u.val ≠ v.val := fun h => hp (Subtype.ext h)
      simp [hp, hv]
  · simp only [ite_eq_right hi, MulZeroClass.mul_zero, coordinates_zero, zero_smul]
    have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    exact (ite_eq_right huv).symm

lemma evaluation_natural [Fintype I] [Fintype J]
    {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    testTransform Q p q α M * evaluationMatrix Q q α (K := K) =
      evaluationMatrix Q p α (K := K) * M := by
  apply Matrix.ext
  intro u j
  exact (testMatrix_evaluation Q p q α hM u j).trans (evaluation_mul Q p α M u j).symm

lemma coevaluation_natural [Fintype I] [Fintype J]
    {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    coevaluationMatrix Q p α (K := K) * testTransform Q p q α M =
      M * coevaluationMatrix Q q α (K := K) := by
  apply Matrix.ext
  intro i u
  exact (coevaluation_testMatrix Q p q α hM i u).trans (mul_coevaluation Q q α M i u).symm

namespace BasedComplex.Map

variable [Fintype I] [Fintype J]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

noncomputable def test (f : Map Q E F) (α : V) :
    Map Q (E.testComplex Q α) (F.testComplex Q α) where
  matrix := testTransform Q E.placement F.placement α f.matrix
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := testMatrix_degree Q α f.degree
  commute := by
    change testTransform Q _ _ α E.differential * _ =
      _ * testTransform Q _ _ α F.differential
    rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ f.entries, f.commute]

noncomputable def cotest (f : Map Q E F) (α : V) :
    Map Q (E.cotestComplex Q α) (F.cotestComplex Q α) where
  matrix := testTransform Q E.placement F.placement α f.matrix
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := cotestMatrix_degree Q α f.degree
  commute := by
    change testTransform Q _ _ α E.differential * _ =
      _ * testTransform Q _ _ α F.differential
    rw [testTransform_mul Q α _ E.entries, testTransform_mul Q α _ f.entries, f.commute]

end BasedComplex.Map
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
