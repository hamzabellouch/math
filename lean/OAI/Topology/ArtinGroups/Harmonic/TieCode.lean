import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Block
import OAI.Topology.ArtinGroups.Harmonic.Coset

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceHeight_eq_blocks {P R:Deligne M} (h:sourceHeight M P=sourceHeight M R) (k:ℕ) :
    sourceBlock M P k=sourceBlock M R k := by
  apply (sourceBlockRank_eq_iff M (Or.inr ⟨P,k,rfl⟩) (Or.inr ⟨R,k,rfl⟩)).mp
  exact congrArg (fun z:Colex (ℕ→₀ℕ)=>(ofColex z) k) h

lemma sourceHeight_ne_of_lt {P R:Deligne M} (h:P<R) : sourceHeight M P≠sourceHeight M R := by
  intro he
  have hb:=sourceHeight_eq_blocks M he 0
  have hs:sourceSecondary M P 0=sourceSecondary M R 0:=
    congrArg (fun b:SourceBlock S=>(ofLex (ofLex b).2).2) hb
  rw [sourceSecondary_zero,sourceSecondary_zero] at hs
  have hc:P.val.1.ncard<R.val.1.ncard:=
    Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)
  rw [Set.ncard_eq_toFinset_card',Set.ncard_eq_toFinset_card'] at hc
  have hp:P.val.1.toFinset.card=Fintype.card P.val.1:=Set.toFinset_card _
  have hr:R.val.1.toFinset.card=Fintype.card R.val.1:=Set.toFinset_card _
  omega

lemma sourceDeligne_countable : Countable (Deligne M) := by
  let :Countable (Artin M):=Function.Surjective.countable (PresentedGroup.mk_surjective (braidRelators M))
  apply Function.Injective.countable (f:=fun P:Deligne M=>(P.val.1,sourceCosetRepresentative M P))
  intro P R h
  have ht:P.val.1=R.val.1:=congrArg (fun z:Set S × Artin M=>z.1) h
  have hx:sourceCosetRepresentative M P=sourceCosetRepresentative M R:=congrArg (fun z:Set S × Artin M=>z.2) h
  apply Subtype.ext
  apply Prod.ext
  · exact ht
  · rw [sourceCosetRepresentative_spec,sourceCosetRepresentative_spec,ht,hx]

noncomputable def sourceTieCode (P:Deligne M) : ℕ :=
  letI:=sourceDeligne_countable M
  letI:=Encodable.ofCountable (Deligne M)
  Encodable.encode P

lemma sourceTieCode_injective : Function.Injective (sourceTieCode M) := by
  let :=sourceDeligne_countable M
  let :=Encodable.ofCountable (Deligne M)
  exact Encodable.encode_injective

noncomputable def sourceVertexKey (P:Deligne M) : Lex (Colex (ℕ→₀ℕ) × ℕ) :=
  toLex (sourceHeight M P,sourceTieCode M P)

def SourceEarlier (P R:Deligne M) : Prop := sourceVertexKey M P<sourceVertexKey M R

lemma sourceVertexKey_injective : Function.Injective (sourceVertexKey M) := by
  intro P R h
  apply sourceTieCode_injective M
  exact congrArg (fun k:Lex (Colex (ℕ→₀ℕ) × ℕ)=>(ofLex k).2) h

theorem sourceEarlier_wellFounded : WellFounded (SourceEarlier M) :=
  InvImage.wf (sourceVertexKey M) wellFounded_lt

lemma sourceEarlier_trichotomy (P R:Deligne M) :
    SourceEarlier M P R ∨ P=R ∨ SourceEarlier M R P := by
  rcases lt_trichotomy (sourceVertexKey M P) (sourceVertexKey M R) with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (sourceVertexKey_injective M h))
  · exact Or.inr (Or.inr h)

lemma sourceEarlier_iff_of_comparable {P R:Deligne M} (h:P<R ∨ R<P) :
    SourceEarlier M P R ↔ sourceHeight M P<sourceHeight M R := by
  have hn:sourceHeight M P≠sourceHeight M R:=by
    rcases h with h|h
    · exact sourceHeight_ne_of_lt M h
    · exact Ne.symm (sourceHeight_ne_of_lt M h)
  change sourceVertexKey M P<sourceVertexKey M R ↔ _
  rw [Prod.Lex.lt_iff]
  simp only [sourceVertexKey,ofLex_toLex,hn,false_and,or_false]

end HarmonicArtin

end OAI
