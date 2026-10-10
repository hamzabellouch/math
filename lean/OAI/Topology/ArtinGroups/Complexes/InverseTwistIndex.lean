import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Quivers.SelfCornerEquiv
import OAI.Topology.ArtinGroups.Complexes.Reindex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

noncomputable instance testIndexDecidableEq (p : I → GeneratorPlacement V) (α : V) :
    DecidableEq (TestIndex Q p α) := Classical.decEq _

abbrev InverseTwistIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
    TestIndex Q E.placement α ⊕ I ⊕ TestIndex Q E.placement α

noncomputable instance inverseTwistIndexDecidableEq
    (E : BasedComplex Q (K := K) I) (α : V) : DecidableEq (InverseTwistIndex Q E α) :=
  Classical.decEq _

noncomputable def inverseTwistIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    InverseTwistIndex Q E α ≃
      (TestIndex Q (E.negativeTwist Q α).placement α ⊕ (I ⊕ TestIndex Q E.placement α)) where
  toFun
    | .inl u => .inl ⟨.inl u.1, u.2⟩
    | .inr (.inl u) => .inl ⟨.inr u, selfCornerEquiv Q hn α false⟩
    | .inr (.inr (.inl u)) => .inl ⟨.inr u, selfCornerEquiv Q hn α true⟩
    | .inr (.inr (.inr (.inl i))) => .inr (.inl i)
    | .inr (.inr (.inr (.inr u))) => .inr (.inr u)
  invFun
    | .inl ⟨.inl i, p⟩ => .inl ⟨i, p⟩
    | .inl ⟨.inr u, p⟩ => if (selfCornerEquiv Q hn α).symm p then
        .inr (.inr (.inl u)) else .inr (.inl u)
    | .inr (.inl i) => .inr (.inr (.inr (.inl i)))
    | .inr (.inr u) => .inr (.inr (.inr (.inr u)))
  left_inv u := by
    rcases u with u | u | u | i | u <;> rfl
  right_inv u := by
    rcases u with ⟨i | u, p⟩ | i | u
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
    · rfl

noncomputable def normalizedInverseTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (InverseTwistIndex Q E α) :=
  ((E.negativeTwist Q α).positiveTwist Q α).reindex Q (inverseTwistIndexEquiv Q hn E α)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
