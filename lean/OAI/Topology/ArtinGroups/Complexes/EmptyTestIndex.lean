import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseWordAction
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma far_test_empty (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) : IsEmpty (TestIndex Q E.placement α) :=
  ⟨fun p=>hE p.1 (Q.corner_target_mem_neighborhood hα p.2)⟩

def emptyTestIndex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) : I ≃ I ⊕ TestIndex Q E.placement α where
  toFun:=Sum.inl
  invFun
    | .inl i=>i
    | .inr p=>h.false p |>.elim
  left_inv _:=rfl
  right_inv k:=by cases k with
    | inl i=>rfl
    | inr p=>exact (h.false p).elim

omit [DecidableEq I] in
lemma negativeTwist_empty_reindex (E:BasedComplex Q (K:=K) I) (α:V)
    (h:IsEmpty (TestIndex Q E.placement α)) :
    (E.negativeTwist Q α).reindex Q (emptyTestIndex Q E α h)=E := by
  apply ext_placement_differential Q <;> rfl

noncomputable def negativeTwistFar (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) : HomotopyEquivalence Q (E.negativeTwist Q α) E := by
  let h:=far_test_empty Q E U hE α hα
  have e:=(E.negativeTwist Q α).reindexHomotopyEquivalence Q (emptyTestIndex Q E α h)
  rw [negativeTwist_empty_reindex] at e
  exact e

lemma classNegativeTwist_far (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (α:V) (hα:α∈U) :
    classNegativeTwist Q α (classOfComplex Q E)=classOfComplex Q E :=
  classOfComplex_eq Q (negativeTwistFar Q E U hE α hα)

lemma inverseWord_far (E:BasedComplex Q (K:=K) I) (U:Set V)
    (hE:∀ i,(E.placement i).color∉Q.closedNeighborhood U)
    (w:List V) (hw:∀ α∈w,α∈U) :
    inverseWordAction Q w (classOfComplex Q E)=classOfComplex Q E := by
  induction w with
  | nil=>rfl
  | cons α w ih=>
    rw [inverseWordAction,classNegativeTwist_far Q E U hE α (hw α (by simp))]
    exact ih (fun β hβ=>hw β (by simp [hβ]))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
