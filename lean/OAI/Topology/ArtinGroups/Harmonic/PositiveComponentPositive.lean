import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveSupportComponent
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponent

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_positive (p:S⊕Unit→ℝ) (i:S⊕Unit) (hi:0<p i)
    (j:S⊕Unit) (hj:j∈sourcePositiveComponent M p i) : 0<p j := by
  change Relation.ReflTransGen _ i j at hj
  induction hj with
  | refl => exact hi
  | tail _ hbc _ => exact hbc.2.2

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_connected (p:S⊕Unit→ℝ) (i:S⊕Unit) :
    ∀j l:sourcePositiveComponent M p i,
      Relation.ReflTransGen (fun a b:sourcePositiveComponent M p i=>framedCartan M a b<0) j l := by
  let I:=sourcePositiveComponent M p i
  have hi:i∈I:=Relation.ReflTransGen.refl
  have hroot:∀j:I,Relation.ReflTransGen (fun a b:I=>framedCartan M a b<0) ⟨i,hi⟩ j := by
    rintro ⟨j,hj⟩
    change Relation.ReflTransGen _ i j at hj
    induction hj with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail hbc.2.1
  intro j l
  have hrev:=Relation.ReflTransGen.swap _ _ (hroot j)
  have hj:Relation.ReflTransGen (fun a b:I=>framedCartan M a b<0) j ⟨i,hi⟩:=
    Relation.ReflTransGen.mono (by intro a b h; dsimp [Function.swap] at h; rwa [framedCartan_symm] at h) _ _ hrev
  exact hj.trans (hroot l)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_spec (p:S⊕Unit→ℝ) (i:S⊕Unit) (hi:0<p i) :
    PositiveSupportComponent (framedCartan M) p (sourcePositiveComponent M p i) := by
  refine ⟨⟨i,Relation.ReflTransGen.refl⟩,sourcePositiveComponent_positive M p i hi,
    sourcePositiveComponent_connected M p i,?_⟩
  intro j hj l hjl hl
  exact hj.tail ⟨sourcePositiveComponent_positive M p i hi j hj,hjl,hl⟩

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_eq (p:S⊕Unit→ℝ) (i:S⊕Unit) (I:Set (S⊕Unit))
    (hI:PositiveSupportComponent (framedCartan M) p I) (hi:i∈I) :
    sourcePositiveComponent M p i=I := by
  ext j
  constructor
  · intro hj
    change Relation.ReflTransGen _ i j at hj
    induction hj with
    | refl => exact hi
    | tail _ hbc ih => exact hI.2.2.2 _ ih _ hbc.2.1 hbc.2.2
  · intro hj
    exact Relation.ReflTransGen.lift ((↑):I→S⊕Unit)
      (fun a b hab=>⟨hI.2.1 a a.property,hab,hI.2.1 b b.property⟩)
      ⟨i,hi⟩ ⟨j,hj⟩ (hI.2.2.1 ⟨i,hi⟩ ⟨j,hj⟩)

omit [LinearOrder S] in
lemma sourceNullSign_iff (p:ℕ→₀(S⊕Unit→ℝ)) (k:ℕ) (i:S⊕Unit) (hi:0<p k i) :
    SourceNullSign M p k i ↔ harmonicPositiveSign (framedCartan M) (.inr ()) p k i := by
  constructor
  · rintro ⟨h0,hf,hr,hb⟩
    refine ⟨h0,sourcePositiveComponent M (p k) i,Relation.ReflTransGen.refl,hf,
      sourcePositiveComponent_spec M (p k) i hi,hr,?_⟩
    intro d hd j hj
    apply hb j _ d hd
    rcases hj with hj|⟨a,ha,haj⟩
    · exact Or.inl hj
    · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩
  · rintro ⟨h0,I,hiI,hf,hI,hr,hb⟩
    have he:=sourcePositiveComponent_eq M (p k) i I hI hiI
    refine ⟨h0,?_,?_,?_⟩
    · rwa [he]
    · rwa [he]
    · intro j hj d hd
      apply hb d hd j
      change j∈sourcePositiveComponent M (p k) i ∨
        ∃a∈sourcePositiveComponent M (p k) i,framedCartan M j a<0 at hj
      rw [he] at hj
      rcases hj with hj|⟨a,ha,hja⟩
      · exact Or.inl hj
      · exact Or.inr ⟨a,ha,by rwa [framedCartan_symm]⟩

omit [LinearOrder S] in
lemma sourceSignAt_neg_iff (p:ℕ→₀(S⊕Unit→ℝ)) (k:ℕ) (i:S⊕Unit)
    (hp:0≤p k i) : sourceSignAt M p k i= -1 ↔
    0<p k i ∧ ¬harmonicPositiveSign (framedCartan M) (.inr ()) p k i := by
  by_cases hz:p k i=0
  · simp [sourceSignAt,hz]
  have hi:0<p k i:=lt_of_le_of_ne hp (Ne.symm hz)
  rw [sourceSignAt,ite_eq_right hz,←sourceNullSign_iff M p k i hi]
  by_cases hn:SourceNullSign M p k i <;> simp [hn,hi]

end HarmonicArtin

end OAI
