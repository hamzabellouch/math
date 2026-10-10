import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma braidCore_to_firstTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inl v)) =
      match i with
      | .inr (.inl u) => if u = v then arrowBasis Q (e.reverse Q).arrow else 0
      | _ => 0 := by
  rcases i with u | u | u | u | i
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, evaluationMatrix, SimpleEdge.corner_val, pathBasis_arrow,
    Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte]

lemma braidFirstSource_to_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u : TestIndex Q E.placement α) (j : BraidCoreIndex Q E α β) :
    (normalizedBraidTwist Q hn E e).differential
      (.inl u) (.inr (.inr (.inr (.inr j)))) =
      match j with
      | .inr (.inr (.inl v)) => -projectiveIdentity Q (testPlacement Q E.placement α) u v
      | _ => 0 := by
  rcases j with v | v | v | v | j
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, selfCornerEquiv_false, pathBasis_vertex,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]
  simp only [projectiveIdentity, Matrix.diagonal_apply, testPlacement]
  apply congrArg Neg.neg
  by_cases hi : u.1 = v.1
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    dsimp only at hi
    subst j
    simp only [ite_true, cornerPath_left, pathBasis_coordinates]
    by_cases hp : p = q
    · subst q
      simp
    · have hpq : p.val ≠ q.val := fun h => hp (Subtype.ext h)
      simp [hp, hpq]
  · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    simp only [ite_eq_right hi, ite_eq_right huv, MulZeroClass.mul_zero, coordinates_zero, zero_smul]

omit [DecidableEq I] in
lemma braidCore_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inr (.inr (.inl v)))) = 0 := by
  rcases i with u | u | u | u | i
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, Sum.inr_ne_inl, ↓reduceIte,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]

omit [DecidableEq I] in
lemma braidFirstSource_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inl u) (.inr (.inr (.inr (.inl v)))) = 0 := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    selfCornerEquiv_false, selfCornerEquiv_true, pathBasis_vertex]
  simp only [_root_.mul_neg, mul_smul, vertexId_mul_self]
  simp only [map_neg, Pi.neg_apply, coordinates_smul]
  have hz : pathCoordinates Q (vertexId Q (K := K) α) (.inr (.inr α)) = 0 := by
    rw [← pathBasis_vertex, pathBasis_coordinates]
    rfl
  simp only [hz, MulZeroClass.mul_zero, neg_zero, zero_smul]

omit [DecidableEq I] in
lemma braidSecondSource_to_firstTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inl v)) = 0 := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    evaluationMatrix, Sum.inl_ne_inr, ↓reduceIte]

omit [Fintype V] in
lemma arrowBasis_reverse (a : A) :
    arrowBasis Q (K := K) a * arrowBasis Q (Q.reverse a) = tokenBasis Q (Q.source a) := by
  apply ext
  · rw [vertex_mul]
    funext i
    simp [arrowBasis, tokenBasis, vertex]
  · rw [arrow_mul]
    funext b
    simp [arrowBasis, tokenBasis, vertex, arrow, leftScale, rightScale]
  · rw [token_mul]
    funext i
    simp only [arrowBasis, tokenBasis, vertex, token, arrow, backtrack, Pi.single_apply,
      Pi.zero_apply, MulZeroClass.mul_zero,
      Pi.add_apply, zero_add]
    rw [Finset.sum_eq_single a]
    · simp [eq_comm]
    · intro b _ hb
      simp [hb]
    · simp

omit [DecidableEq I] in
lemma braidSecondSource_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (u v : TestIndex Q E.placement α) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inl u))) (.inr (.inr (.inr (.inl v)))) =
      -projectiveIdentity Q (testPlacement Q E.placement α) u v := by
  simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, SimpleEdge.corner_val, pathBasis_arrow,
    selfCornerEquiv_true, Sum.inl.injEq, projectiveIdentity, Matrix.diagonal_apply,
    testPlacement, SimpleEdge.reverse_arrow]
  by_cases h : u = v
  · simp only [ite_eq_left h, arrowBasis_reverse, e.source]
    rw [← pathBasis_token, pathBasis_coordinates, ite_eq_left rfl, one_smul]
  · simp only [ite_eq_right h, MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
