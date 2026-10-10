import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDetector
import OAI.Topology.ArtinGroups.Complexes.DiagonalVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

def LinearMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).vertex = 0 ∧ (f i j).token = 0

namespace BasedComplex
lemma supertrace_linear (E : BasedComplex Q (K := K) I)
    {f : Matrix I I (Q.Zigzag K)} (hf : LinearMatrix Q f) : supertrace Q E f = 0 := by
  change (∑ i, cochainSign (K := K) (E.placement i).cochain * trace Q (f i i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  have ht : trace Q (f i i) = 0 := by
    change (∑ α, (f i i).token α) = 0
    rw [(hf i i).2]
    simp only [Pi.zero_apply, Finset.sum_const_zero]
  rw [ht, MulZeroClass.mul_zero]

lemma cochainSign_ne_zero (n : ℤ) : cochainSign (K := K) n ≠ 0 := by
  intro h
  have hh := cochainSign_mul_self (K := K) n
  rw [h, MulZeroClass.zero_mul] at hh
  exact zero_ne_one hh

variable [DecidableEq I]

lemma linear_selfCycle_boundary_zero (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) (hd : homDimension Q E E 0 0 ≤ 1)
    {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E 0 0)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E 0 0 := by
  apply boundary_of_homDimension_le_one Q E E 0 0 hd (diagonalVertex Q E i)
    (fun _ h => diagonalVertex_boundary Q E hE i 0 0 h) (identity_mem_homCycles Q E)
  · rw [diagonalVertex_identity]
    exact one_ne_zero
  · exact hf
  · exact congrFun (hlin i i).1 (E.placement i).color

lemma linear_selfCycle_boundary_two (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) (hd : homDimension Q E E 0 2 ≤ 1)
    {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E 0 2)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E 0 2 := by
  apply boundary_of_homDimension_le_one Q E E 0 2 hd (supertrace Q E)
    (by rintro _ ⟨g, _, rfl⟩; exact supertrace_boundary Q E g)
    (diagonalToken_mem_homCycles Q E hE i)
  · rw [supertrace_diagonalToken]
    exact cochainSign_ne_zero _
  · exact hf
  · exact supertrace_linear Q E hlin

lemma linear_selfCycle_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (hcap : ∀ n v, homDimension Q E E n v ≤ 1)
    (hsupp : ∀ n v, n ≠ 0 ∨ (v ≠ 0 ∧ v ≠ 2) → homDimension Q E E n v = 0)
    (n v : ℤ) {f : Matrix I I (Q.Zigzag K)} (hf : f ∈ homCycles Q E E n v)
    (hlin : LinearMatrix Q f) : f ∈ homBoundaries Q E E n v := by
  by_cases hI : Nonempty I
  · let i : I := Classical.choice hI
    by_cases hn : n = 0
    · subst n
      by_cases hv₀ : v = 0
      · subst v
        exact linear_selfCycle_boundary_zero Q E hE i (hcap 0 0) hf hlin
      · by_cases hv₂ : v = 2
        · subst v
          exact linear_selfCycle_boundary_two Q E hE i (hcap 0 2) hf hlin
        · exact boundary_of_homDimension_zero Q E E 0 v
            (hsupp 0 v (Or.inr ⟨hv₀, hv₂⟩)) hf
    · exact boundary_of_homDimension_zero Q E E n v (hsupp n v (Or.inl hn)) hf
  · have hz : f = 0 := by
      apply Matrix.ext
      intro i _
      exact (hI ⟨i⟩).elim
    rw [hz]
    exact Submodule.zero_mem _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
