import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestPlacement
import OAI.Topology.ArtinGroups.Complexes.Reindex
import OAI.Topology.ArtinGroups.Cancellation.BlockPivot
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential
import OAI.Topology.ArtinGroups.Complexes.Identity

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

abbrev ActedIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {i : I // (E.placement i).color = α}

abbrev AmplitudeCoreIndex (E : BasedComplex Q (K := K) I) (α : V) :=
  {u : TestIndex Q E.placement α // Path.length u.2.val ≠ 0} ⊕
    {i : I // (E.placement i).color ≠ α}

noncomputable instance amplitudeCoreFintype (E : BasedComplex Q (K := K) I) (α : V) :
    Fintype (AmplitudeCoreIndex Q E α) := by
  classical
  unfold AmplitudeCoreIndex
  infer_instance

noncomputable instance amplitudeCoreDecidable (E : BasedComplex Q (K := K) I) (α : V) :
    DecidableEq (AmplitudeCoreIndex Q E α) := fun a b => instDecidableEqSum a b

def unitTest (E : BasedComplex Q (K := K) I) (α : V) (i : ActedIndex Q E α) :
    TestIndex Q E.placement α :=
  ⟨i.val, ⟨.inl α, rfl, i.property.symm⟩⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma unitTest_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (unitTest Q E α) := by
  intro i j h
  exact Subtype.ext (congrArg Sigma.fst h)

def amplitudeIndexMap (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α →
      TestIndex Q E.placement α ⊕ I
  | .inl i => .inl (unitTest Q E α i)
  | .inr (.inl i) => .inr i.val
  | .inr (.inr (.inl u)) => .inl u.val
  | .inr (.inr (.inr i)) => .inr i.val

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma amplitudeIndexMap_injective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Injective (amplitudeIndexMap Q E α) := by
  intro i j h
  rcases i with i | i | u | i <;> rcases j with j | j | v | j
  all_goals dsimp only [amplitudeIndexMap] at h
  all_goals try cases h
  · exact congrArg Sum.inl (unitTest_injective Q E α (Sum.inl.inj h))
  · have hv := v.property
    rw [← Sum.inl.inj h] at hv
    exact (hv rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext (Sum.inr.inj h))
  · exact (j.property ((Sum.inr.inj h) ▸ i.property)).elim
  · have hu := u.property
    rw [Sum.inl.inj h] at hu
    exact (hu rfl).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (Subtype.ext (Sum.inl.inj h))
  · exact (i.property ((Sum.inr.inj h).symm ▸ j.property)).elim
  · exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (Subtype.ext (Sum.inr.inj h))

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma amplitudeIndexMap_surjective (E : BasedComplex Q (K := K) I) (α : V) :
    Function.Surjective (amplitudeIndexMap Q E α) := by
  intro u
  rcases u with ⟨i, ⟨v | a | v, hs, ht⟩⟩ | i
  · dsimp only [Path.source, Path.target] at hs ht
    subst v
    exact ⟨.inl ⟨i, ht.symm⟩, rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inl a), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · exact ⟨.inr (.inr (.inl ⟨⟨i, ⟨.inr (.inr v), hs, ht⟩⟩, by norm_num [Path.length]⟩)), rfl⟩
  · by_cases hi : (E.placement i).color = α
    · exact ⟨.inr (.inl ⟨i, hi⟩), rfl⟩
    · exact ⟨.inr (.inr (.inr ⟨i, hi⟩)), rfl⟩

noncomputable def amplitudeIndexEquiv (E : BasedComplex Q (K := K) I) (α : V) :
    ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α ≃
      TestIndex Q E.placement α ⊕ I :=
  Equiv.ofBijective (amplitudeIndexMap Q E α)
    ⟨amplitudeIndexMap_injective Q E α, amplitudeIndexMap_surjective Q E α⟩

noncomputable def normalizedAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K)
      (ActedIndex Q E α ⊕ ActedIndex Q E α ⊕ AmplitudeCoreIndex Q E α) :=
  (E.positiveTwist Q α).reindex Q (amplitudeIndexEquiv Q E α)

noncomputable def amplitudePivot (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedAmplitudeTwist Q E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color i := i.property
  cochain i := by change (E.placement i.val).cochain = (E.placement i.val).cochain - 1 + 1; omega
  internal i := by change (E.placement i.val).internal = (E.placement i.val).internal + 0; omega
  entry i j := by
    change evaluationMatrix Q E.placement α (unitTest Q E α i) j.val =
      (1 : K) • projectiveIdentity Q
        (fun j => (normalizedAmplitudeTwist Q E α).placement (.inl j)) i j
    simp only [evaluationMatrix, unitTest, pathBasis_vertex, one_smul,
      projectiveIdentity, Matrix.diagonal_apply]
    change (if i.val = j.val then vertexId Q (K := K) α else 0) =
      (if i = j then vertexId Q (K := K) α else 0)
    simp only [Subtype.val_inj]

noncomputable def reducedAmplitudeTwist (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (AmplitudeCoreIndex Q E α) :=
  (amplitudePivot Q E α).reduced Q

noncomputable def amplitudeTwistReduction (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (reducedAmplitudeTwist Q E α) :=
  ((E.positiveTwist Q α).reindexHomotopyEquivalence Q (amplitudeIndexEquiv Q E α)).trans Q
    ((amplitudePivot Q E α).reductionEquivalence Q)

lemma reducedAmplitudeTwist_placement (E : BasedComplex Q (K := K) I) (α : V) :
    (reducedAmplitudeTwist Q E α).placement =
      fun i => match i with
      | .inl u => ⟨α, (E.placement u.val.1).cochain - 1,
          (E.placement u.val.1).internal + Path.length u.val.2.val⟩
      | .inr i => E.placement i.val := by
  funext i
  cases i <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
