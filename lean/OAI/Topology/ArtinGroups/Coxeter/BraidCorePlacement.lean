import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Coxeter.BraidSecondPivot
import OAI.Topology.ArtinGroups.Quivers.ExtArrow

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def braidCorePlacement (E : BasedComplex Q (K := K) I) (α β : V) :
    BraidCoreIndex Q E α β → GeneratorPlacement V
  | .inl u => ⟨α, (E.placement u.1).cochain - 2,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩
  | .inr (.inl u) => ⟨β, (E.placement u.1).cochain - 2,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩
  | .inr (.inr (.inl u)) => ⟨α, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr (.inr (.inl u))) => ⟨β, (E.placement u.1).cochain - 1,
      (E.placement u.1).internal + Path.length u.2.val⟩
  | .inr (.inr (.inr (.inr i))) => E.placement i

omit [DecidableEq I] in
lemma reducedBraidTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E e).placement = braidCorePlacement Q E α β := by
  funext i
  rcases i with u | u | u | u | i
  · change (⟨α, (E.placement u.1).cochain - 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩ : GeneratorPlacement V) = _
    congr 1
    omega
  · change (⟨β, (E.placement u.1).cochain - 1 - 1,
      (E.placement u.1).internal + Path.length u.2.val + 1⟩ : GeneratorPlacement V) = _
    congr 1
    omega
  · rfl
  · rfl
  · rfl

def braidCoreSwap (E : BasedComplex Q (K := K) I) (α β : V) :
    BraidCoreIndex Q E α β ≃ BraidCoreIndex Q E β α where
  toFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr (.inl u)) => .inr (.inr (.inr (.inl u)))
    | .inr (.inr (.inr (.inl u))) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inr i))) => .inr (.inr (.inr (.inr i)))
  invFun
    | .inl u => .inr (.inl u)
    | .inr (.inl u) => .inl u
    | .inr (.inr (.inl u)) => .inr (.inr (.inr (.inl u)))
    | .inr (.inr (.inr (.inl u))) => .inr (.inr (.inl u))
    | .inr (.inr (.inr (.inr i))) => .inr (.inr (.inr (.inr i)))
  left_inv u := by rcases u with u | u | u | u | i <;> rfl
  right_inv u := by rcases u with u | u | u | u | i <;> rfl

lemma reducedBraidTwist_swap (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E (e.reverse Q)).reindex Q (braidCoreSwap Q E α β) =
      reducedBraidTwist Q hn E e := by
  apply ext_placement_differential Q
  · change (reducedBraidTwist Q hn E (e.reverse Q)).placement ∘ _ = _
    rw [reducedBraidTwist_placement, reducedBraidTwist_placement]
    funext i
    rcases i with u | u | u | u | i <;> rfl
  · change (reducedBraidTwist Q hn E (e.reverse Q)).differential.submatrix _ _ = _
    rw [reducedBraidTwist_differential, reducedBraidTwist_differential]
    apply Matrix.ext
    intro i j
    rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
    all_goals simp only [Matrix.submatrix_apply, braidCoreSwap, Equiv.coe_fn_mk,
      braidCoreDifferential, SimpleEdge.reverse_reverse]

noncomputable def braidTwistReduction (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α)
      (reducedBraidTwist Q hn E e) := by
  classical
  letI : DecidableEq (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
      BraidCoreIndex Q E α β) := braidFirstReducedDecidable Q E α β
  let f := (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α).reindexHomotopyEquivalence Q
    (braidTwistIndexEquiv Q hn E e)
  let g := (braidFirstPivot Q hn E e).reductionEquivalence Q
  let h := (braidSecondPivot Q hn E e).reductionEquivalence Q
  exact (f.trans Q g).trans Q h

noncomputable def adjacent_positiveTwists (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    HomotopyEquivalence Q (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α)
      (((E.positiveTwist Q β).positiveTwist Q α).positiveTwist Q β) := by
  classical
  let f := braidTwistReduction Q hn E e
  let g := braidTwistReduction Q hn E (e.reverse Q)
  let k := (reducedBraidTwist Q hn E (e.reverse Q)).reindexHomotopyEquivalence Q
    (braidCoreSwap Q E α β)
  have k' : HomotopyEquivalence Q (reducedBraidTwist Q hn E (e.reverse Q))
      (reducedBraidTwist Q hn E e) := by
    rw [← reducedBraidTwist_swap Q hn E e]
    exact k
  exact (f.trans Q (k'.symm Q)).trans Q (g.symm Q)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
