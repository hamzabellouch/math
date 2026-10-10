import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

noncomputable def reverseTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α ≃
      ((TestIndex Q E.placement α ⊕ I) ⊕ TestIndex Q (E.positiveTwist Q α).placement α) where
  toFun
    | .inl u => .inl (.inl u)
    | .inr (.inl u) => .inr ⟨.inl u, selfCornerEquiv Q hn α false⟩
    | .inr (.inr (.inl u)) => .inr ⟨.inl u, selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inl i))) => .inl (.inr i)
    | .inr (.inr (.inr (.inr u))) => .inr ⟨.inr u.1, u.2⟩
  invFun
    | .inl (.inl u) => .inl u
    | .inl (.inr i) => .inr (.inr (.inr (.inl i)))
    | .inr ⟨.inl u, p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inl u)) else .inr (.inl u)
    | .inr ⟨.inr i, p⟩ => .inr (.inr (.inr (.inr ⟨i, p⟩)))
  left_inv u := by
    rcases u with u | u | u | i | u <;> rfl
  right_inv u := by
    rcases u with (u | i) | ⟨u | i, p⟩
    · rfl
    · rfl
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = p
        simpa only [h] using he
    · rfl

noncomputable def normalizedReverseTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (InverseTwistIndex Q E α) :=
  ((E.positiveTwist Q α).negativeTwist Q α).reindex Q (reverseTwistIndexEquiv Q hn E α)

lemma normalizedReverseTwist_placement (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (normalizedReverseTwist Q hn E α).placement = inverseTwistPlacement Q E α := by
  funext i
  rcases i with u | u | u | i | u
  · rfl
  · change (⟨α, (E.placement u.1).cochain - 1 + 1,
      (E.placement u.1).internal + Path.length u.2.val + 0 - 2⟩ : GeneratorPlacement V) = _
    simp only [sub_add_cancel, add_zero]
    rfl
  · change (⟨α, (E.placement u.1).cochain - 1 + 1,
      (E.placement u.1).internal + Path.length u.2.val + 2 - 2⟩ : GeneratorPlacement V) = _
    simp only [sub_add_cancel, add_sub_cancel_right]
    rfl
  · rfl
  · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
