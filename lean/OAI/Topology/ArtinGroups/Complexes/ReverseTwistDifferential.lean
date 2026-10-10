import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistIndexEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def reverseTwistDifferential (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inl u, .inr (.inl v) => testToken Q E.placement α u v
  | .inl u, .inr (.inr (.inl v)) => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inl u, .inr (.inr (.inr (.inl j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inl v) => testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) =>
      -projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => -unitContraction Q E.placement α u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => E.differential i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => coevaluationMatrix Q E.placement α i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      -testTransform Q E.placement E.placement α E.differential u v
  | _, _ => 0

lemma coordinates_tokenBasis_mul (α : V) (x : Q.Zigzag K) (p : Path V A) :
    pathCoordinates Q (tokenBasis Q α * x) p =
      (x * pathBasis Q (Path.dual Q p)).vertex α := by
  rw [coordinates_trace, _root_.mul_assoc, trace_mul_comm, trace_mul_tokenBasis]

lemma normalizedReverseTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedReverseTwist Q hn E α).differential = reverseTwistDifferential Q E α := by
  change ((E.positiveTwist Q α).negativeTwist Q α).differential.submatrix
    (reverseTwistIndexEquiv Q hn E α) (reverseTwistIndexEquiv Q hn E α) = _
  rw [negativeTwist_differential]
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [Matrix.submatrix_apply, reverseTwistIndexEquiv, Equiv.coe_fn_mk,
    Matrix.of_apply, reverseTwistDifferential, Matrix.fromBlocks, testTransform,
    scalarCornerMatrix, testMatrix]
  all_goals simp only [positiveTwist_differential, Matrix.fromBlocks, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.of_apply, testTransform, scalarCornerMatrix, testMatrix,
    Sum.elim_inl, Sum.elim_inr, MulZeroClass.mul_zero, coordinates_zero, zero_smul,
    neg_zero, selfCornerEquiv_false, selfCornerEquiv_true]
  all_goals try simp only [coevaluationMatrix, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte, selfCornerEquiv_false,
    selfCornerEquiv_true, Path.dual, pathBasis_vertex, pathBasis_token, projectiveIdentity,
    Matrix.diagonal_apply, testPlacement, testToken]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg]
  all_goals try simp only [vertexId_mul_self]
  all_goals try (refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl)
  all_goals try (
    have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
      simpa only [Path.target, pathBasis_token] using
        (pathBasis_right Q (K := K) (.inr (.inr α)))
    simp only [ht, pathCoordinates_vertex, pathCoordinates_token]
    simp only [vertexId, tokenBasis, vertex, token, Pi.single_apply, ite_true, Pi.zero_apply]
    first
      | exact congrArg (fun k : K => k • vertexId Q (K := K) α)
          (_root_.mul_one (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
            E.differential u.1 v.1) v.2.val))
      | exact (congrArg (fun k : K => k • vertexId Q (K := K) α)
          (MulZeroClass.mul_zero (pathCoordinates Q (pathBasis Q (K := K) u.2.val *
            E.differential u.1 v.1) v.2.val))).trans (zero_smul K _))
  · apply congrArg Neg.neg
    by_cases hi : u.1 = v.1
    · rcases u with ⟨i, u⟩
      rcases v with ⟨j, v⟩
      dsimp only at hi
      subst j
      simp only [evaluationMatrix, ite_true, cornerPath_left, pathBasis_coordinates]
      by_cases hp : u = v
      · subst v
        simp
      · have hp' : u.val ≠ v.val := fun h => hp (Subtype.ext h)
        simp [hp, hp']
    · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
      simp only [evaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        coordinates_zero, zero_smul, ite_eq_right huv]
  · apply congrArg Neg.neg
    by_cases hi : u.1 = v.1
    · simp only [evaluationMatrix, ite_eq_left hi, coordinates_tokenBasis_mul,
        unitContraction]
    · simp only [evaluationMatrix, ite_eq_right hi, MulZeroClass.mul_zero,
        coordinates_zero, zero_smul, unitContraction]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
