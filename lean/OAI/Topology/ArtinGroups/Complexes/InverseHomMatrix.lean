import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistProjectionCommute
import OAI.Topology.ArtinGroups.Complexes.PositiveHomTransform

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def inverseHomMatrix (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    (f : Matrix I J (Q.Zigzag K)) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q F α) (Q.Zigzag K) :=
  Matrix.fromBlocks (cochainSign (K := K) n • testTransform Q E.placement F.placement α f) 0 0
    (Matrix.fromBlocks (testTransform Q E.placement F.placement α f) 0 0
      (Matrix.fromBlocks (testTransform Q E.placement F.placement α f) 0 0
        (Matrix.fromBlocks f 0 0
          (cochainSign (K := K) n • testTransform Q E.placement F.placement α f))))

omit [DecidableEq I] [DecidableEq J] in
lemma inverseHomMatrix_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    (positiveHomTransform Q (E.negativeTwist Q α) (F.negativeTwist Q α) α n
      (negativeHomTransform Q E F α n f)).submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) =
      inverseHomMatrix Q E F α n f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, inverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseHomMatrix, positiveHomTransform, negativeHomTransform, Matrix.fromBlocks,
    Matrix.smul_apply,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, smul_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token, smul_smul]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    have hv : (vertexId Q (K := K) α).vertex α = 1 := by
      simp only [vertex_vertexId, Pi.single_eq_same]
    have htv : (tokenBasis Q (K := K) α).vertex α = 0 := rfl
    have htt : (tokenBasis Q (K := K) α).token α = 1 := by
      change (Pi.single α (1 : K) : V → K) α = 1
      exact Pi.single_eq_same α 1
    simp only [hv, htv, htt, token_vertexId, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals first
    | exact zero_smul K (vertexId Q α)
    | exact congrArg (fun c : K => c • vertexId Q α)
        (by rw [← _root_.mul_assoc, cochainSign_mul_self]; exact _root_.one_mul _)

omit [DecidableEq I] [DecidableEq J] in
lemma reverseHomMatrix_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (α : V) (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    (negativeHomTransform Q (E.positiveTwist Q α) (F.positiveTwist Q α) α n
      (positiveHomTransform Q E F α n f)).submatrix
      (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α) =
      inverseHomMatrix Q E F α n f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, reverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseHomMatrix, positiveHomTransform, negativeHomTransform, Matrix.fromBlocks,
    Matrix.smul_apply,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, smul_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token, smul_smul]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    have hv : (vertexId Q (K := K) α).vertex α = 1 := by
      simp only [vertex_vertexId, Pi.single_eq_same]
    have htv : (tokenBasis Q (K := K) α).vertex α = 0 := rfl
    have htt : (tokenBasis Q (K := K) α).token α = 1 := by
      change (Pi.single α (1 : K) : V → K) α = 1
      exact Pi.single_eq_same α 1
    simp only [hv, htv, htt, token_vertexId, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals first
    | exact zero_smul K (vertexId Q α)
    | exact congrArg (fun c : K => c • vertexId Q α)
        (by rw [← _root_.mul_assoc, cochainSign_mul_self]; exact _root_.one_mul _)

lemma inverseHomMatrix_projection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseHomMatrix Q E F α n f * inverseTwistProjection Q F α =
      inverseTwistProjection Q E α * f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseHomMatrix, inverseTwistProjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  · exact congrArg (fun a => a u j) (evaluation_natural Q α hf)
  · exact congrArg (fun a => a i j)
      ((projectiveIdentity_mul Q hf).trans (mul_projectiveIdentity Q hf).symm).symm

lemma inverseHomMatrix_extract (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseTwistInjection Q E α * inverseHomMatrix Q E F α n f *
      inverseTwistProjection Q F α = f := by
  rw [Matrix.mul_assoc, inverseHomMatrix_projection Q E F α n hf,
    ← Matrix.mul_assoc, inverseTwist_targetEquation]
  exact projectiveIdentity_mul Q hf

lemma reverseHomMatrix_projection (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    inverseHomMatrix Q E F α n f * reverseTwistProjection Q F α =
      reverseTwistProjection Q E α * f := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseHomMatrix, reverseTwistProjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_zero]
  · exact congrArg (fun a => -a u j) (evaluation_natural Q α hf)
  · exact congrArg (fun a => a i j)
      ((projectiveIdentity_mul Q hf).trans (mul_projectiveIdentity Q hf).symm).symm

lemma reverseHomMatrix_extract (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (α : V) (n : ℤ)
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f) :
    reverseTwistInjection Q E α * inverseHomMatrix Q E F α n f *
      reverseTwistProjection Q F α = f := by
  rw [Matrix.mul_assoc, reverseHomMatrix_projection Q E F α n hf,
    ← Matrix.mul_assoc, reverseTwist_targetEquation]
  exact projectiveIdentity_mul Q hf

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
