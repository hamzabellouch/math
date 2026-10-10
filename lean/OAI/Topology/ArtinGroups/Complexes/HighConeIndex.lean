import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Complexes.DownClosed

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def highConeIndex (T:Set I) :
    ((Tᶜ:Set I) ⊕ ((Tᶜ:Set I) ⊕ T)) ≃ (I ⊕ (Tᶜ:Set I)) where
  toFun
    | .inl i=>.inl i.val
    | .inr (.inl j)=>.inr j
    | .inr (.inr k)=>.inl k.val
  invFun
    | .inl i=>if h:i∈T then .inr (.inr ⟨i,h⟩) else .inl ⟨i,h⟩
    | .inr j=>.inr (.inl j)
  left_inv k:=by
    rcases k with i|(j|k)
    · simp only [dite_eq_right i.property]
    · rfl
    · simp only [dite_eq_left k.property]
  right_inv k:=by
    rcases k with i|j
    · dsimp only
      split_ifs <;> rfl
    · rfl

noncomputable def highConeNormalized (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) :=
  ((highProjection Q E T h).cone Q).reindex Q (highConeIndex T)

noncomputable def highConePivot (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) : BlockPivot Q (highConeNormalized Q E T h) where
  coefficient:=1
  nonzero:=one_ne_zero
  color _:=rfl
  cochain i:=by change (E.placement i).cochain=(E.placement i).cochain-1+1; omega
  internal _:=rfl
  entry i j:=by
    change (if (i:I)=(j:I) then vertexId Q (K:=K) (E.placement i).color else 0)=
      1 • (if i=j then vertexId Q (K:=K) (E.placement i).color else 0)
    simp only [one_smul,Subtype.val_inj]

noncomputable def highConeReduction (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) : HomotopyEquivalence Q ((highProjection Q E T h).cone Q)
      ((highConePivot Q E T h).reduced Q) :=
  (((highProjection Q E T h).cone Q).reindexHomotopyEquivalence Q (highConeIndex T)).trans Q
    ((highConePivot Q E T h).reductionEquivalence Q)

omit [Fintype V] [DecidableEq A] in
lemma highConeRetained_level (E:BasedComplex Q (K:=K) I) (T:Set I)
    (h:DownClosed Q E T) (i:T) :
    (((highConePivot Q E T h).reduced Q).placement i).level=(E.placement i).level-1 := by
  change (E.placement i).cochain-1+(E.placement i).internal=
    (E.placement i).cochain+(E.placement i).internal-1
  omega

noncomputable def highPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (hE:∀ i,(E.placement i).level≤q) :
    {i:I // (E.placement i).level=q} ≃ ((lowerLevelSet Q E (q-1))ᶜ:Set I) where
  toFun i:=⟨i.val,by change ¬(E.placement i.val).level≤q-1; have hi:=i.property; omega⟩
  invFun i:=⟨i.val,by
    have hi:=i.property
    have hu:=hE i.val
    change ¬(E.placement i.val).level≤q-1 at hi
    omega⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype V] [DecidableEq A] in
lemma highRestriction_top_eq_layer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) :
    classOfComplex Q (upperTruncation Q E hE (q-1))=
      classLayer Q q (classOfComplex Q E) := by
  have he:(upperTruncation Q E hE (q-1)).reindex Q (highPureIndex Q E q hhi)=
      E.pureLayer Q hE q := by
    apply ext_placement_differential Q <;> rfl
  rw [classLayer_minimal]
  exact (classOfComplex_reindex Q _ (highPureIndex Q E q hhi)).trans
    (by rw [he])

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
