import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def edgeContraction (p : I → GeneratorPlacement V)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (TestIndex Q p β) (TestIndex Q p α) K :=
  fun u v => if u.1 = v.1 then
    pathCoordinates Q (arrowBasis Q e.arrow * pathBasis Q u.2.val) v.2.val else 0

namespace BasedComplex

noncomputable def braidCoreDifferential (E : BasedComplex Q (K := K) I)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (BraidCoreIndex Q E α β) (BraidCoreIndex Q E α β) (Q.Zigzag K)
  | .inl u, .inl v => scalarCornerMatrix Q α (testMatrix Q E.placement E.placement β E.differential) u v
  | .inr (.inl u), .inr (.inl v) => scalarCornerMatrix Q β (testMatrix Q E.placement E.placement α E.differential) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => -testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inr (.inr (.inl u))), .inr (.inr (.inr (.inl v))) => -testTransform Q E.placement E.placement β E.differential u v
  | .inl u, .inr (.inr (.inl v)) => -scalarCornerMatrix Q α (edgeContraction Q E.placement e) u v
  | .inl u, .inr (.inr (.inr (.inl v))) => if u = v then arrowBasis Q e.arrow else 0
  | .inr (.inl u), .inr (.inr (.inl v)) => if u = v then arrowBasis Q (e.reverse Q).arrow else 0
  | .inr (.inl u), .inr (.inr (.inr (.inl v))) => -scalarCornerMatrix Q β (edgeContraction Q E.placement (e.reverse Q)) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr j))) => evaluationMatrix Q E.placement α u j
  | .inr (.inr (.inr (.inl u))), .inr (.inr (.inr (.inr j))) => evaluationMatrix Q E.placement β u j
  | .inr (.inr (.inr (.inr i))), .inr (.inr (.inr (.inr j))) => E.differential i j
  | _, _ => 0

noncomputable def braidRawCoreDifferential (E : BasedComplex Q (K := K) I)
    {α β : V} (e : SimpleEdge Q α β) :
    Matrix (BraidCoreIndex Q E α β) (BraidCoreIndex Q E α β) (Q.Zigzag K)
  | .inr (.inl _), .inr (.inr (.inl _)) => 0
  | i, j => braidCoreDifferential Q E e i j

lemma arrowBasis_right_vertex (a : A) :
    arrowBasis Q (K := K) a * vertexId Q (Q.target a) = arrowBasis Q a := by
  simpa only [Path.target, pathBasis_arrow] using
    pathBasis_right Q (K := K) (.inr (.inl a))

lemma arrowBasis_coordinates_self (a : A) :
    pathCoordinates Q (arrowBasis Q (K := K) a) (.inr (.inl a)) = 1 := by
  rw [← pathBasis_arrow, pathBasis_coordinates, ite_eq_left rfl]

lemma simpleEdge_arrow_right {α β : V} (e : SimpleEdge Q α β) :
    arrowBasis Q (K := K) e.arrow * vertexId Q β = arrowBasis Q e.arrow := by
  simpa only [e.target] using arrowBasis_right_vertex Q (K := K) e.arrow

lemma normalizedBraidTwist_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i j : BraidCoreIndex Q E α β) :
    (normalizedBraidTwist Q hn E e).differential
      (.inr (.inr (.inr (.inr i)))) (.inr (.inr (.inr (.inr j)))) =
      braidRawCoreDifferential Q E e i j := by
  rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
  all_goals simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
    braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_apply, Matrix.neg_apply, testTransform, scalarCornerMatrix, testMatrix,
    braidRawCoreDifferential, braidCoreDifferential,
    MulZeroClass.mul_zero, coordinates_zero, zero_smul, neg_zero,
    SimpleEdge.corner_val, pathBasis_arrow]
  all_goals try simp only [_root_.mul_neg, mul_smul, map_neg, Pi.neg_apply,
    coordinates_smul, neg_smul, neg_neg, simpleEdge_arrow_right Q e,
    simpleEdge_arrow_right Q (e.reverse Q),
    arrowBasis_coordinates_self, _root_.mul_one]
  all_goals try simp only [evaluationMatrix, edgeContraction,
    Sum.inr.injEq, Sum.inl.injEq, Sum.inr_ne_inl, Sum.inl_ne_inr, ↓reduceIte,
    SimpleEdge.corner_val, pathBasis_arrow]
  all_goals try (refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl)
  · split_ifs with h
    · have hx := congrArg (fun x : TestIndex Q (E.positiveTwist Q α).placement β => x.1) h
      cases hx
    · rfl
  · split_ifs <;> simp only [MulZeroClass.mul_zero, coordinates_zero]
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    refine @ite_cond_congr _ _ _ ?_ ?_ _ _ ?_
    apply propext
    constructor
    · intro h
      have hi := congrArg (fun x : TestIndex Q (E.positiveTwist Q α).placement β => x.1) h
      have hij : i = j := Sum.inr.inj hi
      subst j
      have hpq : p = q := by cases h; rfl
      cases hpq
      rfl
    · intro h
      cases h
      rfl
  · split_ifs <;> simp only [MulZeroClass.mul_zero, coordinates_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
