import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ConeMap
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistIndexEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def inverseTwistMap {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q F α) (Q.Zigzag K) :=
  Matrix.fromBlocks (testTransform Q E.placement F.placement α f.matrix) 0 0
    (Matrix.fromBlocks (testTransform Q E.placement F.placement α f.matrix) 0 0
      (Matrix.fromBlocks (testTransform Q E.placement F.placement α f.matrix) 0 0
        (Matrix.fromBlocks f.matrix 0 0
          (testTransform Q E.placement F.placement α f.matrix))))

omit [DecidableEq I] [DecidableEq J] in
lemma inverseTwistMap_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (α : V) :
    ((f.negativeTwist Q α).positiveTwist Q α).matrix.submatrix
      (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn F α) =
      inverseTwistMap Q f α := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, inverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseTwistMap, Map.positiveTwist, Map.negativeTwist, Map.coneMap,
    Map.coconeMap, Map.test, Map.cotest, Matrix.fromBlocks,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals exact zero_smul K _

omit [DecidableEq I] [DecidableEq J] in
lemma reverseTwistMap_normalized (hn : ∀ a, Q.source a ≠ Q.target a)
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (α : V) :
    ((f.positiveTwist Q α).negativeTwist Q α).matrix.submatrix
      (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn F α) =
      inverseTwistMap Q f α := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, reverseTwistIndexEquiv, Equiv.coe_fn_mk,
    inverseTwistMap, Map.positiveTwist, Map.negativeTwist, Map.coneMap,
    Map.coconeMap, Map.test, Map.cotest, Matrix.fromBlocks,
    testTransform, scalarCornerMatrix, testMatrix, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals simp only [mul_smul, coordinates_smul, pathBasis_vertex, pathBasis_token]
  all_goals (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [vertexId_mul_self, ht, pathCoordinates_vertex, pathCoordinates_token]
    simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true, Pi.zero_apply,
      _root_.mul_one, MulZeroClass.mul_zero])
  all_goals exact zero_smul K _

lemma inverseTwistProjection_natural {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (α : V) :
    inverseTwistMap Q f α * inverseTwistProjection Q F α =
      inverseTwistProjection Q E α * f.matrix := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseTwistMap, inverseTwistProjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  · exact congrArg (fun a => a u j) (evaluation_natural Q α f.entries)
  · exact congrArg (fun a => a i j)
      ((projectiveIdentity_mul Q f.entries).trans (mul_projectiveIdentity Q f.entries).symm).symm

lemma inverseTwistInjection_natural {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (α : V) :
    f.matrix * inverseTwistInjection Q F α =
      inverseTwistInjection Q E α * inverseTwistMap Q f α := by
  apply Matrix.ext
  intro i j
  rcases j with u | u | u | j | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type,
    inverseTwistMap, inverseTwistInjection, Matrix.fromBlocks, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, zero_add, add_zero, mul_neg, neg_mul,
    Finset.sum_neg_distrib]
  · exact congrArg (fun a => -a i u) (coevaluation_natural Q α f.entries).symm
  · exact congrArg (fun a => a i j)
      ((mul_projectiveIdentity Q f.entries).trans (projectiveIdentity_mul Q f.entries).symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
