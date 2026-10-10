import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A : Type*} (Q : ReversibleQuiver V A)

def OrthogonalVertices (α β : V) : Prop :=
  α ≠ β ∧ ∀ a, Q.source a = α → Q.target a ≠ β

lemma OrthogonalVertices.symm {α β : V} (h : OrthogonalVertices Q α β) :
    OrthogonalVertices Q β α := by
  refine ⟨h.1.symm, ?_⟩
  intro a hs ht
  exact h.2 (Q.reverse a) ((Q.source_reverse a).trans ht)
    ((Q.target_reverse a).trans hs)

lemma no_corner_of_orthogonal {α β : V} (h : OrthogonalVertices Q α β)
    (p : CornerPath Q α β) : False := by
  rcases p with ⟨v | a | v, hs, ht⟩
  · exact h.1 (hs.symm.trans ht)
  · exact h.2 a hs ht
  · exact h.1 (hs.symm.trans ht)

namespace BasedComplex

variable {K I J : Type*} [Field K] [Fintype V] [Fintype A]
  [DecidableEq V] [DecidableEq A] [Fintype I] [Fintype J]

omit [Fintype V] [DecidableEq A] in
@[ext] lemma ext_placement_differential
    {E F : BasedComplex Q (K := K) I} (hp : E.placement = F.placement)
    (hd : E.differential = F.differential) : E = F := by
  cases E
  cases F
  cases hp
  cases hd
  rfl

variable [DecidableEq I] [DecidableEq J]

noncomputable def HomotopyEquivalence.symm
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (h : HomotopyEquivalence Q E F) : HomotopyEquivalence Q F E where
  forward := h.backward
  backward := h.forward
  sourceHomotopy := h.targetHomotopy
  targetHomotopy := h.sourceHomotopy
  sourceEntries := h.targetEntries
  targetEntries := h.sourceEntries
  sourceDegree := h.targetDegree
  targetDegree := h.sourceDegree
  sourceEquation := h.targetEquation
  targetEquation := h.sourceEquation

abbrev CommuteTwistIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement β ⊕ I

noncomputable def commuteTwistIndexEquiv (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    CommuteTwistIndex Q E α β ≃
      (TestIndex Q (E.positiveTwist Q β).placement α ⊕ (TestIndex Q E.placement β ⊕ I)) where
  toFun
    | .inl u => .inl ⟨.inr u.1, u.2⟩
    | .inr u => .inr u
  invFun
    | .inl ⟨.inl _, p⟩ => (no_corner_of_orthogonal Q h p).elim
    | .inl ⟨.inr i, p⟩ => .inl ⟨i, p⟩
    | .inr u => .inr u
  left_inv u := by
    rcases u with u | u <;> rfl
  right_inv u := by
    rcases u with ⟨u | i, p⟩ | u
    · exact (no_corner_of_orthogonal Q h p).elim
    · rfl
    · rfl

noncomputable def normalizedCommuteTwist (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    BasedComplex Q (K := K) (CommuteTwistIndex Q E α β) :=
  ((E.positiveTwist Q β).positiveTwist Q α).reindex Q (commuteTwistIndexEquiv Q E h)

def commuteTwistPlacement (E : BasedComplex Q (K := K) I) (α β : V) :
    CommuteTwistIndex Q E α β → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inl u) => ⟨β, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr i) => E.placement i

omit [DecidableEq I] in
lemma normalizedCommuteTwist_placement (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E h).placement = commuteTwistPlacement Q E α β := by
  funext u
  rcases u with u | u | i <;> rfl

noncomputable def commuteTwistDifferential (E : BasedComplex Q (K := K) I) (α β : V) :
    Matrix (CommuteTwistIndex Q E α β) (CommuteTwistIndex Q E α β) (Q.Zigzag K)
  | .inl u, .inl v => -testTransform Q E.placement E.placement α E.differential u v
  | .inr (.inl u), .inr (.inl v) => -testTransform Q E.placement E.placement β E.differential u v
  | .inl u, .inr (.inr j) => evaluationMatrix Q E.placement α u j
  | .inr (.inl u), .inr (.inr j) => evaluationMatrix Q E.placement β u j
  | .inr (.inr i), .inr (.inr j) => E.differential i j
  | _, _ => 0

omit [DecidableEq I] in
lemma normalizedCommuteTwist_differential (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E h).differential = commuteTwistDifferential Q E α β := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | i <;> rcases j with v | v | j
  all_goals simp only [normalizedCommuteTwist, reindex, Matrix.submatrix_apply,
    commuteTwistIndexEquiv, Equiv.coe_fn_mk, positiveTwist_differential,
    Matrix.fromBlocks, commuteTwistDifferential, Matrix.neg_apply, Matrix.of_apply,
    Matrix.zero_apply, Sum.elim_inl, Sum.elim_inr, testTransform, scalarCornerMatrix, testMatrix,
    evaluationMatrix, Sum.inr_ne_inl, Sum.inr.injEq, ↓reduceIte]
  refine @ite_cond_congr _ _ _ ?_ ?_ _ _ (Sum.inr.injEq _ _)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
