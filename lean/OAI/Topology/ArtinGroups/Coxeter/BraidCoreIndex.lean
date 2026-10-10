import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Quivers.SelfCornerEquiv
import OAI.Topology.ArtinGroups.Complexes.Reindex
import OAI.Topology.ArtinGroups.Quivers.SimpleEdge

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev BraidCoreIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement β ⊕ TestIndex Q E.placement α ⊕
    TestIndex Q E.placement α ⊕ TestIndex Q E.placement β ⊕ I

abbrev BraidTwistIndex (E : BasedComplex Q (K := K) I) (α β : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
    (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕ BraidCoreIndex Q E α β)

noncomputable instance braidCoreFintype (E : BasedComplex Q (K := K) I) (α β : V) :
    Fintype (BraidCoreIndex Q E α β) := by
  classical
  unfold BraidCoreIndex
  infer_instance

noncomputable instance braidTwistFintype (E : BasedComplex Q (K := K) I) (α β : V) :
    Fintype (BraidTwistIndex Q E α β) := by
  classical
  unfold BraidTwistIndex
  infer_instance

noncomputable def braidTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BraidTwistIndex Q E α β ≃
      (TestIndex Q ((E.positiveTwist Q α).positiveTwist Q β).placement α ⊕
        (TestIndex Q (E.positiveTwist Q α).placement β ⊕ (TestIndex Q E.placement α ⊕ I))) where
  toFun
    | .inl u => .inl ⟨.inr (.inl u), selfCornerEquiv Q hn α false⟩
    | .inr (.inl u) => .inr (.inr (.inl u))
    | .inr (.inr (.inl u)) => .inl ⟨.inl ⟨.inl u, (e.reverse Q).corner Q⟩, e.corner Q⟩
    | .inr (.inr (.inr (.inl u))) => .inl ⟨.inr (.inl u), selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inr (.inl u)))) => .inl ⟨.inl ⟨.inr u.1, u.2⟩, e.corner Q⟩
    | .inr (.inr (.inr (.inr (.inr (.inl u))))) => .inr (.inl ⟨.inl u, (e.reverse Q).corner Q⟩)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))) => .inl ⟨.inr (.inr u.1), u.2⟩
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u))))))) => .inr (.inl ⟨.inr u.1, u.2⟩)
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i))))))) => .inr (.inr (.inr i))
  invFun
    | .inl ⟨.inl ⟨.inl u, _⟩, _⟩ => .inr (.inr (.inl u))
    | .inl ⟨.inl ⟨.inr i, p⟩, _⟩ => .inr (.inr (.inr (.inr (.inl ⟨i, p⟩))))
    | .inl ⟨.inr (.inl u), p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inr (.inl u))) else .inl u
    | .inl ⟨.inr (.inr i), p⟩ => .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, p⟩))))))
    | .inr (.inl ⟨.inl u, _⟩) => .inr (.inr (.inr (.inr (.inr (.inl u)))))
    | .inr (.inl ⟨.inr i, p⟩) => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, p⟩)))))))
    | .inr (.inr (.inl u)) => .inr (.inl u)
    | .inr (.inr (.inr i)) => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr i)))))))
  left_inv u := by
    rcases u with u | u | u | u | u | u | u | u | i <;> rfl
  right_inv u := by
    rcases u with ⟨⟨u | i, p⟩ | (u | i), q⟩ | (⟨u | i, p⟩ | (u | i))
    · have hp : p = (e.reverse Q).corner Q := (e.reverse Q).corner_unique Q p
      have hq : q = e.corner Q := e.corner_unique Q q
      cases hp
      cases hq
      rfl
    · have hq : q = e.corner Q := e.corner_unique Q q
      cases hq
      rfl
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply q
      cases h : (selfCornerEquiv Q hn α).symm q
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = q
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 2
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = q
        simpa only [h] using he
    · rfl
    · have hp : p = (e.reverse Q).corner Q := (e.reverse Q).corner_unique Q p
      cases hp
      rfl
    · rfl
    · rfl
    · rfl

noncomputable def normalizedBraidTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BasedComplex Q (K := K) (BraidTwistIndex Q E α β) :=
  (((E.positiveTwist Q α).positiveTwist Q β).positiveTwist Q α).reindex Q
    (braidTwistIndexEquiv Q hn E e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
