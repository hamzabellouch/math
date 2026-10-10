import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.GeneratorPlacement

namespace OAI

namespace HarmonicArtin

def GeneratorPlacement.level {V : Type*} (p : GeneratorPlacement V) : ℤ :=
  p.cochain + p.internal

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma homogeneous_nonzero_degree {a : ℤ} {x : Q.Zigzag K}
    (ha : Homogeneous Q a x) (hx : x ≠ 0) : a = 0 ∨ a = 1 ∨ a = 2 := by
  by_contra h
  have h0 : a ≠ 0 := fun he => h (Or.inl he)
  have h1 : a ≠ 1 := fun he => h (Or.inr (Or.inl he))
  have h2 : a ≠ 2 := fun he => h (Or.inr (Or.inr he))
  apply hx
  exact Zigzag.ext (ha.1 h0) (ha.2.1 h1) (ha.2.2 h2)

lemma positive_homogeneous_nonzero_degree {a : ℤ} {x : Q.Zigzag K}
    (ha : Homogeneous Q a x) (hv : x.vertex = 0) (hx : x ≠ 0) : a = 1 ∨ a = 2 := by
  rcases homogeneous_nonzero_degree Q ha hx with h | h | h
  · subst a
    exact (hx (Zigzag.ext hv (ha.2.1 (by decide)) (ha.2.2 (by decide)))).elim
  · exact Or.inl h
  · exact Or.inr h

namespace BasedComplex

variable {I : Type*} [Fintype I]

theorem differential_level (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) {i j : I} (hij : E.differential i j ≠ 0) :
    (E.placement j).level = (E.placement i).level ∨
    (E.placement j).level = (E.placement i).level - 1 := by
  have hc : (E.placement j).cochain = (E.placement i).cochain + 1 := by
    by_contra h
    exact hij ((E.degree i j).1 h)
  have hu := positive_homogeneous_nonzero_degree Q (E.degree i j).2 (hE i j) hij
  simp only [zero_add] at hu
  dsimp only [GeneratorPlacement.level]
  omega

noncomputable def restrict (E : BasedComplex Q (K := K) I) (T : Set I) [Fintype T]
    (hT : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∉ T,
      E.differential i k * E.differential k j = 0) :
    BasedComplex Q (K := K) T := by
  classical
  exact {
    placement := fun i => E.placement i
    differential := fun i j => E.differential i j
    entries := ⟨fun i j => E.entries.1 i j, fun i j => E.entries.2 i j⟩
    degree := fun i j => E.degree i j
    square_zero := by
      apply Matrix.ext
      intro i j
      change (∑ k : T, E.differential i k * E.differential k j) = 0
      have he := congrArg (fun M : Matrix I I (Q.Zigzag K) => M i j) E.square_zero
      change (∑ k, E.differential i k * E.differential k j) = 0 at he
      rw [← he]
      apply Fintype.sum_of_injective (Subtype.val : T → I) Subtype.val_injective
      · intro k hk
        apply hT i i.property j j.property k
        intro hkT
        exact hk ⟨⟨k, hkT⟩, rfl⟩
      · intro k
        rfl }

lemma restrict_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (T : Set I) [Fintype T] (hT : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∉ T,
      E.differential i k * E.differential k j = 0) :
    (E.restrict Q T hT).IsMinimal Q := by
  intro i j
  exact hE i j

lemma differential_intermediate_level (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) {i j k : I} (hi : E.differential i k ≠ 0)
    (hj : E.differential k j ≠ 0) :
    (E.placement j).level ≤ (E.placement k).level ∧
    (E.placement k).level ≤ (E.placement i).level := by
  have h₁ := E.differential_level Q hE hi
  have h₂ := E.differential_level Q hE hj
  omega

lemma pureLayer_intermediate (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (d : ℤ) : ∀ i ∈ {i | (E.placement i).level = d},
      ∀ j ∈ {j | (E.placement j).level = d},
      ∀ k ∉ {k | (E.placement k).level = d},
      E.differential i k * E.differential k j = 0 := by
  intro i hi j hj k hk
  by_cases h₁ : E.differential i k = 0
  · rw [h₁]
    exact MulZeroClass.zero_mul _
  by_cases h₂ : E.differential k j = 0
  · rw [h₂]
    exact MulZeroClass.mul_zero _
  have hb := E.differential_intermediate_level Q hE h₁ h₂
  exact (hk (le_antisymm (hi ▸ hb.2) (hj ▸ hb.1))).elim

noncomputable def pureLayer (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) :
    BasedComplex Q (K := K) (↑{i | (E.placement i).level = d} : Type _) :=
  E.restrict Q _ (E.pureLayer_intermediate Q hE d)

lemma pureLayer_linear (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (d : ℤ) (i j : {i // (E.placement i).level = d}) :
    ((E.pureLayer Q hE d).differential i j).vertex = 0 ∧
    ((E.pureLayer Q hE d).differential i j).token = 0 := by
  change (E.differential i j).vertex = 0 ∧ (E.differential i j).token = 0
  refine ⟨hE i j, ?_⟩
  by_cases hz : E.differential i j = 0
  · rw [hz]
    rfl
  have hc : (E.placement j).cochain = (E.placement i).cochain + 1 := by
    by_contra h
    exact hz ((E.degree i j).1 h)
  have hi := i.property
  have hj := j.property
  dsimp only [GeneratorPlacement.level] at hi hj
  apply (E.degree i j).2.2.2
  omega

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
