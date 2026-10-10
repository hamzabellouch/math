import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement
import OAI.Topology.ArtinGroups.Complexes.ActedIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev NegativeAmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 2} ⊕
    {i : I // (E.placement i).color ≠ α}

noncomputable instance negativeAmplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (NegativeAmplitudeCoreIndex Q E α) := by
  classical
  unfold NegativeAmplitudeCoreIndex
  infer_instance

noncomputable instance negativeAmplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (NegativeAmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

def tokenTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inr (.inr α), rfl, i.property.symm⟩⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma tokenTest_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (tokenTest Q E α) := by
  intro i j h
  exact Subtype.ext (congrArg Sigma.fst h)

def negativeAmplitudeIndexMap (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α →
      I ⊕ TestIndex Q E.placement α
  | .inl i => .inl i.val
  | .inr (.inl i) => .inr (tokenTest Q E α i)
  | .inr (.inr (.inl u)) => .inr u.val
  | .inr (.inr (.inr i)) => .inl i.val

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma negativeAmplitudeIndexMap_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (negativeAmplitudeIndexMap Q E α) := by
  intro i j h
  rcases i with i | i | u | i <;> rcases j with j | j | v | j
  all_goals dsimp only [negativeAmplitudeIndexMap] at h
  all_goals try cases h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · exact (j.property ((Sum.inl.inj h) ▸ i.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (tokenTest_injective Q E α (Sum.inr.inj h))
  · have hv := v.property
    rw [← Sum.inr.inj h] at hv
    exact (hv rfl).elim
  · have hu := u.property
    rw [Sum.inr.inj h] at hu
    exact (hu rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (Subtype.ext (Sum.inr.inj h))
  · exact (i.property ((Sum.inl.inj h).symm ▸ j.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (Subtype.ext (Sum.inl.inj h))

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma negativeAmplitudeIndexMap_surjective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Surjective (negativeAmplitudeIndexMap Q E α) := by
  intro u
  rcases u with i | ⟨i, ⟨v | a | v, hs, ht⟩⟩
  · by_cases hi : (E.placement i).color = α
    · exact ⟨.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨.inr (.inr (.inr ⟨i, hi⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inl v, hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inl a), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · dsimp only [Path.source, Path.target] at hs ht
    subst v
    exact ⟨.inr (.inl ⟨i, ht.symm⟩), rfl⟩

noncomputable def negativeAmplitudeIndexEquiv (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α ≃
      I ⊕ TestIndex Q E.placement α :=
  Equiv.ofBijective (negativeAmplitudeIndexMap Q E α)
    ⟨negativeAmplitudeIndexMap_injective Q E α, negativeAmplitudeIndexMap_surjective Q E α⟩

noncomputable def normalizedNegativeAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K)
      (ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ NegativeAmplitudeCoreIndex Q E α) :=
  (E.negativeTwist Q α).reindex Q (negativeAmplitudeIndexEquiv Q E α)

noncomputable def negativeAmplitudePivot (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedNegativeAmplitudeTwist Q E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color i := i.property.symm
  cochain i := by change (E.placement i.val).cochain + 1 = (E.placement i.val).cochain + 1; rfl
  internal i := by change (E.placement i.val).internal + 2 - 2 = (E.placement i.val).internal; omega
  entry i j := by
    change coevaluationMatrix Q E.placement α i.val (tokenTest Q E α j) =
      (1 : K) • projectiveIdentity Q
        (fun j => (normalizedNegativeAmplitudeTwist Q E α).placement (.inl j)) i j
    simp only [coevaluationMatrix, tokenTest, Path.dual, pathBasis_vertex, one_smul,
      projectiveIdentity, Matrix.diagonal_apply]
    change (if i.val = j.val then vertexId Q (K := K) α else 0) =
      (if i = j then vertexId Q (E.placement i.val).color else 0)
    rw [i.property]
    simp only [Subtype.val_inj]

noncomputable def reducedNegativeAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (NegativeAmplitudeCoreIndex Q E α) :=
  (negativeAmplitudePivot Q E α).reduced Q

noncomputable def negativeAmplitudeTwistReduction (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (reducedNegativeAmplitudeTwist Q E α) :=
  ((E.negativeTwist Q α).reindexHomotopyEquivalence Q (negativeAmplitudeIndexEquiv Q E α)).trans Q
    ((negativeAmplitudePivot Q E α).reductionEquivalence Q)

lemma reducedNegativeAmplitudeTwist_placement (E : BasedComplex Q (K := K) I) (α : V) :
    (reducedNegativeAmplitudeTwist Q E α).placement =
      fun i => match i with
      | .inl u => ⟨α, (E.placement u.val.1).cochain + 1,
          (E.placement u.val.1).internal + Path.length u.val.2.val - 2⟩
      | .inr i => E.placement i.val := by
  funext i
  cases i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
