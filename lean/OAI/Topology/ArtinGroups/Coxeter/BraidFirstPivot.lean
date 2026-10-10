import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Cancellation.BlockPivot
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def braidFirstPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BlockPivot Q (normalizedBraidTwist Q hn E e) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain - 1 = (E.placement u.1).cochain - 1 - 1 + 1
    omega
  internal u := by
    change (E.placement u.1).internal + Path.length u.2.val =
      (E.placement u.1).internal + Path.length u.2.val + 0
    omega
  entry u v := by
    simp only [normalizedBraidTwist, reindex, Matrix.submatrix_apply,
      braidTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
      Matrix.fromBlocks, Matrix.of_apply, evaluationMatrix, selfCornerEquiv_false,
      pathBasis_vertex, Sum.inr.injEq, Sum.inl.injEq, Sum.elim_inl, Sum.elim_inr,
      one_smul, projectiveIdentity, Matrix.diagonal_apply]
    refine @ite_cond_congr _ _ _ ?_ ?_ _ _ rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
