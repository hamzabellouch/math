import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Harmonic
import OAI.Topology.ArtinGroups.Harmonic.MultiplicitySum

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

lemma harmonicExtension_zero {ι:Type*} [Fintype ι] (C:Matrix ι ι ℝ) (T:Set ι) :
    harmonicExtension C T 0=0 := by
  funext i
  simp [harmonicExtension,Matrix.mulVec,dotProduct]

lemma harmonicExtension_congr_exterior {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (T:Set ι) {v w:ι→ℝ} (h:∀i,i∉T→v i=w i) :
    harmonicExtension C T v=harmonicExtension C T w := by
  funext i
  by_cases hi:i∈T
  · simp only [harmonicExtension,dite_eq_left hi]
    congr 2
    funext j
    apply Finset.sum_congr rfl
    intro k _
    rw [h k k.property]
  · simp only [harmonicExtension,dite_eq_right hi,h i hi]

lemma finite_harmonic_images {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (A:Set ℝ) (hA:A.Finite) :
    {p:ι→ℝ | ∃ T:Set ι,∃ v:ι→ℝ,(∀i,v i∈A) ∧ p=harmonicExtension C T v}.Finite := by
  have hv:{v:ι→ℝ | ∀i,v i∈A}.Finite := by
    exact Set.Finite.pi' (fun _=>hA)
  have h:((Set.univ:Set (Set ι)) ×ˢ {v:ι→ℝ | ∀i,v i∈A}).Finite :=
    Set.finite_univ.prod hv
  apply (h.image fun Tv=>harmonicExtension C Tv.1 Tv.2).subset
  rintro p ⟨T,v,hv,rfl⟩
  exact ⟨(T,v),⟨Set.mem_univ _,hv⟩,rfl⟩

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceCosetVector_support_finite (P:Deligne M) :
    {k:ℤ | sourceCosetVector M P k≠0}.Finite := by
  apply (sourceMultiplicity_support_finite M (sourceCosetRepresentative M P)).subset
  intro k hk
  by_contra hn
  apply hk
  have hz:sourceMultiplicity M (sourceCosetRepresentative M P) k=0:=not_not.mp hn
  change harmonicExtension _ _ _=0
  rw [hz,harmonicExtension_zero]

noncomputable def sourceCosetSum (P:Deligne M) (k:ℤ) : ℝ :=
  ∑ i,sourceCosetVector M P k i

lemma sourceCosetVector_le_sum (P:Deligne M) (k:ℤ) (i:S⊕Unit) :
    sourceCosetVector M P k i ≤ sourceCosetSum M P k :=
  Finset.single_le_sum (fun j _=>sourceCosetVector_nonneg M P k j) (Finset.mem_univ i)

lemma sourceCosetVector_bounded_finite (B:ℝ) :
    {p:S⊕Unit→ℝ | ∃ P:Deligne M,∃ k:ℤ,sourceCosetSum M P k ≤ B ∧
      p=sourceCosetVector M P k}.Finite := by
  let A:Set ℝ := {0} ∪ {r:ℝ | r≤B ∧ ∃ x k v,r=sourceMultiplicity M x k v}
  have hA:A.Finite := (Set.finite_singleton 0).union (sourceMultiplicity_values_finite M B)
  apply (finite_harmonic_images (framedCartan M) A hA).subset
  rintro p ⟨P,k,hB,rfl⟩
  let T:Set (S⊕Unit) := (Sum.inl : S→S⊕Unit) '' P.val.1
  let v:S⊕Unit→ℝ := fun i=>if i∈T then 0 else sourceCosetVector M P k i
  refine ⟨T,v,?_,?_⟩
  · intro i
    by_cases hi:i∈T
    · exact Or.inl (by simp only [v,ite_eq_left hi,Set.mem_singleton_iff])
    · right
      dsimp only [v]
      rw [ite_eq_right hi]
      refine ⟨(sourceCosetVector_le_sum M P k i).trans hB,?_⟩
      refine ⟨sourceCosetRepresentative M P,k,i,?_⟩
      exact sourceHarmonicAt_outside M P.val.1 _ k i hi
  · change harmonicExtension (framedCartan M) T _=harmonicExtension (framedCartan M) T v
    apply harmonicExtension_congr_exterior
    intro i hi
    simp only [v,ite_eq_right hi]
    exact (sourceHarmonicAt_outside M P.val.1 _ k i hi).symm

end HarmonicArtin

end OAI
