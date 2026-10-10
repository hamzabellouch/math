import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestTransform
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def inverseTwistDifferential (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K) :=
  fun i j => match i, j with
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inl u, .inr (.inl v) => -unitContraction Q E.placement α u v
  | .inl u, .inr (.inr (.inl v)) => -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inl u, .inr (.inr (.inr (.inl j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inl v) => testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => testToken Q E.placement α u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => E.differential i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => coevaluationMatrix Q E.placement α i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      -testTransform Q E.placement E.placement α E.differential u v
  | _, _ => 0

omit [DecidableEq I] in
lemma positiveTwist_differential (E : BasedComplex Q (K := K) I) (α : V) :
    (E.positiveTwist Q α).differential =
      Matrix.fromBlocks (-testTransform Q E.placement E.placement α E.differential)
        (evaluationMatrix Q E.placement α) 0 E.differential := rfl

omit [DecidableEq I] in
lemma negativeTwist_differential (E : BasedComplex Q (K := K) I) (α : V) :
    (E.negativeTwist Q α).differential =
      Matrix.fromBlocks E.differential (coevaluationMatrix Q E.placement α)
        0 (-testTransform Q E.placement E.placement α E.differential) := rfl

lemma normalizedInverseTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedInverseTwist Q hn E α).differential = inverseTwistDifferential Q E α := by
  change ((E.negativeTwist Q α).positiveTwist Q α).differential.submatrix
    (inverseTwistIndexEquiv Q hn E α) (inverseTwistIndexEquiv Q hn E α) = _
  rw [positiveTwist_differential]
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, inverseTwistIndexEquiv, Equiv.coe_fn_mk,
    Matrix.of_apply,
    inverseTwistDifferential, Matrix.fromBlocks, testTransform, scalarCornerMatrix, testMatrix]
  all_goals simp only [negativeTwist_differential, Matrix.fromBlocks, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.of_apply, testTransform, scalarCornerMatrix, testMatrix, Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero,
    coordinates_zero, zero_smul, neg_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals try simp only [evaluationMatrix, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte, selfCornerEquiv_false,
    selfCornerEquiv_true, pathBasis_vertex, pathBasis_token, projectiveIdentity,
    Matrix.diagonal_apply, testPlacement, testToken]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg]
  all_goals try simp only [vertexId_mul_self]
  · simp only [coevaluationMatrix, unitContraction, pathCoordinates_vertex]
    split_ifs <;> simp_all
  · apply congrArg Neg.neg
    change (pathBasis Q (K := K) u.2.val * coevaluationMatrix Q E.placement α u.1 v).token α •
      vertexId Q α = if u = v then vertexId Q α else 0
    by_cases hi : u.1 = v.1
    · rcases u with ⟨i, u⟩
      rcases v with ⟨j, v⟩
      dsimp only at hi
      subst j
      simp only [coevaluationMatrix, ite_true, cornerPath_basis_dual_token]
      by_cases hp : u = v
      · subst v
        simp
      · simp [hp]
    · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
      simp only [coevaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        token_zero, Pi.zero_apply, zero_smul, ite_eq_right huv]
  all_goals
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    try simp only [ht, pathCoordinates_vertex, pathCoordinates_token]
    try simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true,
      Pi.zero_apply]
    first
    | rfl
    | exact congrArg (fun k : K => k • vertexId Q (K := K) α)
        (_root_.mul_one (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
          E.differential u.1 v.1) v.2.val))
    | exact (congrArg (fun k : K => k • vertexId Q (K := K) α)
        (MulZeroClass.mul_zero (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
          E.differential u.1 v.1) v.2.val))).trans (zero_smul K _)
    | refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
