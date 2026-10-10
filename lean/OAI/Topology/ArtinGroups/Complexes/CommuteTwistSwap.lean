import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def commuteTwistSwap (E : BasedComplex Q (K := K) I) (α β : V) :
    CommuteTwistIndex Q E α β ≃ CommuteTwistIndex Q E β α where
  toFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  invFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr i) => .inr (.inr i)
  left_inv u := by rcases u with u | u | i <;> rfl
  right_inv u := by rcases u with u | u | i <;> rfl

omit [DecidableEq I] in
lemma normalizedCommuteTwist_swap (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    (normalizedCommuteTwist Q E (h.symm Q)).reindex Q (commuteTwistSwap Q E α β) =
      normalizedCommuteTwist Q E h := by
  apply ext_placement_differential Q
  · change (normalizedCommuteTwist Q E (h.symm Q)).placement ∘ _ = _
    rw [normalizedCommuteTwist_placement, normalizedCommuteTwist_placement]
    funext i
    rcases i with u | u | i <;> rfl
  · change (normalizedCommuteTwist Q E (h.symm Q)).differential.submatrix _ _ = _
    rw [normalizedCommuteTwist_differential, normalizedCommuteTwist_differential]
    apply Matrix.ext
    intro i j
    rcases i with u | u | i <;> rcases j with v | v | j <;> rfl

noncomputable def orthogonal_positiveTwists (E : BasedComplex Q (K := K) I)
    {α β : V} (h : OrthogonalVertices Q α β) :
    HomotopyEquivalence Q ((E.positiveTwist Q β).positiveTwist Q α)
      ((E.positiveTwist Q α).positiveTwist Q β) := by
  classical
  let f := ((E.positiveTwist Q β).positiveTwist Q α).reindexHomotopyEquivalence Q
    (commuteTwistIndexEquiv Q E h)
  let g := ((E.positiveTwist Q α).positiveTwist Q β).reindexHomotopyEquivalence Q
    (commuteTwistIndexEquiv Q E (h.symm Q))
  let k := (normalizedCommuteTwist Q E (h.symm Q)).reindexHomotopyEquivalence Q
    (commuteTwistSwap Q E α β)
  have k' : HomotopyEquivalence Q (normalizedCommuteTwist Q E (h.symm Q))
      (normalizedCommuteTwist Q E h) := by
    rw [← normalizedCommuteTwist_swap Q E h]
    exact k
  exact (f.trans Q (k'.symm Q)).trans Q (g.symm Q)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
