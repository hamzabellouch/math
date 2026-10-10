import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.HomSpace

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [DecidableEq A] in
lemma testTransform_smul (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (α : V) (r : K) (f : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (r • f) = r • testTransform Q p q α f := by
  apply Matrix.ext
  intro i j
  simp only [testTransform, scalarCornerMatrix, testMatrix, Matrix.smul_apply,
    mul_smul, coordinates_smul, smul_smul]

omit [DecidableEq A] in
lemma testTransform_sub (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (α : V) (f g : Matrix I J (Q.Zigzag K)) :
    testTransform Q p q α (f - g) =
      testTransform Q p q α f - testTransform Q p q α g := by
  simp only [sub_eq_add_neg, testTransform_add, testTransform_neg]

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def positiveHomTransform (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (TestIndex Q E.placement α ⊕ I) (TestIndex Q F.placement α ⊕ J) (Q.Zigzag K) :=
  Matrix.fromBlocks (cochainSign (K := K) n • testTransform Q E.placement F.placement α f)
    0 0 f

noncomputable def negativeHomTransform (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (I ⊕ TestIndex Q E.placement α) (J ⊕ TestIndex Q F.placement α) (Q.Zigzag K) :=
  Matrix.fromBlocks f 0 0
    (cochainSign (K := K) n • testTransform Q E.placement F.placement α f)

lemma positiveHomTransform_entries (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    ProjectiveEntries Q (E.positiveTwist Q α).placement (F.positiveTwist Q α).placement
      (positiveHomTransform Q E F α n f) := by
  have ht := projectiveEntries_smul Q (cochainSign (K := K) n)
    (scalarCornerMatrix_entries Q α (testPlacement Q E.placement α)
      (testPlacement Q F.placement α) (fun _ => rfl) (fun _ => rfl)
        (testMatrix Q E.placement F.placement α f))
  constructor <;> intro i j <;> rcases i with i | i <;> rcases j with j | j
  · exact ht.1 i j
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _
  · exact hf.1 i j
  · exact ht.2 i j
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _
  · exact hf.2 i j

lemma negativeHomTransform_entries (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    ProjectiveEntries Q (E.negativeTwist Q α).placement (F.negativeTwist Q α).placement
      (negativeHomTransform Q E F α n f) := by
  have ht := projectiveEntries_smul Q (cochainSign (K := K) n)
    (scalarCornerMatrix_entries Q α (cotestPlacement Q E.placement α)
      (cotestPlacement Q F.placement α) (fun _ => rfl) (fun _ => rfl)
        (testMatrix Q E.placement F.placement α f))
  constructor <;> intro i j <;> rcases i with i | i <;> rcases j with j | j
  · exact hf.1 i j
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _
  · exact ht.1 i j
  · exact hf.2 i j
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _
  · exact ht.2 i j

lemma positiveHomTransform_degree (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f) :
    MapDegree Q (E.positiveTwist Q α).placement (F.positiveTwist Q α).placement n v
      (positiveHomTransform Q E F α n f) := by
  have ht := mapDegree_smul Q (cochainSign (K := K) n) (testMatrix_degree Q α hf)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (testPlacement Q F.placement α j).cochain - 1 =
        (testPlacement Q E.placement α i).cochain - 1 + n
      omega
    · exact (ht i j).2
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact hf i j

lemma negativeHomTransform_degree (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f) :
    MapDegree Q (E.negativeTwist Q α).placement (F.negativeTwist Q α).placement n v
      (negativeHomTransform Q E F α n f) := by
  have ht := mapDegree_smul Q (cochainSign (K := K) n) (cotestMatrix_degree Q α hf)
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hf i j
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · constructor
    · intro hc
      apply (ht i j).1
      intro he
      apply hc
      change (cotestPlacement Q F.placement α j).cochain + 1 =
        (cotestPlacement Q E.placement α i).cochain + 1 + n
      omega
    · exact (ht i j).2

lemma positiveHomTransform_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    homDifferential Q (E.positiveTwist Q α) (F.positiveTwist Q α) n
      (positiveHomTransform Q E F α n f) =
    positiveHomTransform Q E F α (n + 1) (homDifferential Q E F n f) := by
  change (E.positiveTwist Q α).differential * positiveHomTransform Q E F α n f -
    cochainSign (K := K) n • (positiveHomTransform Q E F α n f * (F.positiveTwist Q α).differential) = _
  rw [positiveTwist_differential, positiveTwist_differential]
  unfold positiveHomTransform
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp only [← sub_eq_add_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, smul_zero,
    testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hf,
    evaluation_natural Q α hf, smul_smul, cochainSign_mul_self, one_smul,
    sub_self, cochainSign_add_one, neg_zero]
  congr 1
  simp [homDifferential, testTransform_sub, testTransform_smul,
    smul_sub, smul_smul, cochainSign_mul_self, neg_smul, smul_neg]

lemma negativeHomTransform_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    homDifferential Q (E.negativeTwist Q α) (F.negativeTwist Q α) n
      (negativeHomTransform Q E F α n f) =
    negativeHomTransform Q E F α (n + 1) (homDifferential Q E F n f) := by
  change (E.negativeTwist Q α).differential * negativeHomTransform Q E F α n f -
    cochainSign (K := K) n • (negativeHomTransform Q E F α n f * (F.negativeTwist Q α).differential) = _
  rw [negativeTwist_differential, negativeTwist_differential]
  unfold negativeHomTransform
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp only [← sub_eq_add_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, smul_zero,
    testTransform_mul Q α _ E.entries, testTransform_mul Q α _ hf,
    coevaluation_natural Q α hf, sub_self, cochainSign_add_one, neg_zero]
  congr 1
  simp [homDifferential, testTransform_sub, testTransform_smul,
    smul_sub, smul_smul, cochainSign_mul_self, neg_smul, smul_neg]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
