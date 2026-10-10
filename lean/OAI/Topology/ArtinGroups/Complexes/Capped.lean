import Mathlib
import OAI.Topology.ArtinGroups.Complexes.RestrictLayer
import OAI.Topology.ArtinGroups.Quivers.PathTwoSelf

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*}

lemma degree_token_support {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q n v M)
    (i : I) (j : J) (w : V) (hne : (M i j).token w ≠ 0) :
    (p i).color = w ∧ (q j).color = w ∧
    (q j).cochain = (p i).cochain + n ∧
    (q j).internal = (p i).internal + v - 2 := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.token w) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.token w) (hc.2 i j)
  have hpv : (p i).color = w := by
    by_contra h
    have hh : w ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color * M i j).token w = (M i j).token w at hleft
    rw [token_mul] at hleft
    simp only [token_vertexId, arrow_vertexId, MulZeroClass.zero_mul,
      backtrack_zero_left, Pi.add_apply, Pi.zero_apply, add_zero] at hleft
    change (vertexId Q (p i).color).vertex w * (M i j).token w = _ at hleft
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.zero_mul] at hleft
    exact hne hleft.symm
  have hqv : (q j).color = w := by
    by_contra h
    have hh : w ≠ (q j).color := Ne.symm h
    change (M i j * vertexId Q (q j).color).token w = (M i j).token w at hright
    rw [token_mul] at hright
    simp only [token_vertexId, arrow_vertexId, MulZeroClass.mul_zero,
      backtrack_zero_right, Pi.add_apply, Pi.zero_apply, zero_add, add_zero] at hright
    change (M i j).token w * (vertexId Q (q j).color).vertex w = _ at hright
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.mul_zero] at hright
    exact hne hright.symm
  have hcq : (q j).cochain = (p i).cochain + n := by
    by_contra h
    have hz := (hd i j).1 h
    exact hne (by rw [hz]; rfl)
  have hiq : (q j).internal = (p i).internal + v - 2 := by
    by_contra h
    have hh : v + (p i).internal - (q j).internal ≠ 2 := by omega
    have hz := (hd i j).2.2.2 hh
    exact hne (by rw [hz]; rfl)
  exact ⟨hpv, hqv, hcq, hiq⟩

namespace BasedComplex
variable [Fintype I] [Fintype J]

def CappedOn (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ) : Prop :=
  ∀ i, (E.placement i).color ∈ U → (E.placement i).level ≤ q

lemma differential_token_level (E : BasedComplex Q (K := K) I) {i j : I}
    (h : (E.placement j).level ≠ (E.placement i).level - 1) :
    (E.differential i j).token = 0 := by
  by_cases hc : (E.placement j).cochain = (E.placement i).cochain + 1
  · apply (E.degree i j).2.2.2
    dsimp only [GeneratorPlacement.level] at h
    omega
  · rw [(E.degree i j).1 hc]
    rfl

lemma capped_incoming_token (E : BasedComplex Q (K := K) I) (U : Set V) (q : ℤ)
    (hcap : E.CappedOn Q U q) (j : I) (hj : (E.placement j).level = q)
    (hU : (E.placement j).color ∈ U) (i : I) :
    pathTwo Q (E.differential i j) = 0 := by
  apply pathTwo_eq_zero Q
  ext w
  by_contra hw
  obtain ⟨hi, hjc, hc, hu⟩ := degree_token_support Q E.entries E.degree i j w hw
  have h : (E.placement i).color ∈ U := by simpa only [hi, hjc] using hU
  have hb := hcap i h
  dsimp only [GeneratorPlacement.level] at hb hj
  omega

lemma extendLayer_coefficient (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : CoefficientMatrix Q f) : CoefficientMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  simp only [extendLayer_entry]
  split_ifs with hi hj
  · exact hf ⟨i, hi⟩ ⟨j, hj⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

lemma capped_matrixTwo_mul_extend (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (U : Set V) (q d : ℤ)
    (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    matrixTwo Q E.differential * extendLayer Q E F q d f = 0 := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [extendLayer_entry]
  split_ifs with ht hj
  · by_cases hU : (E.placement t).color ∈ U
    · change pathTwo Q (E.differential i t) * f ⟨t, ht⟩ ⟨j, hj⟩ = 0
      rw [capped_incoming_token Q E U q hcap t ht hU i, MulZeroClass.zero_mul]
    · rw [hs ⟨t, ht⟩ ⟨j, hj⟩ hU, MulZeroClass.mul_zero]
  · exact MulZeroClass.mul_zero _
  · exact MulZeroClass.mul_zero _

lemma extend_restrictLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ) {f : Matrix I J (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i).level ≠ l ∨ (F.placement j).level ≠ k → f i j = 0) :
    extendLayer Q E F l k (restrictLayer Q E F l k f) = f := by
  apply Matrix.ext
  intro i j
  rw [extendLayer_entry]
  split_ifs with hi hj
  · rfl
  · exact (hs i j (Or.inr hj)).symm
  · exact (hs i j (Or.inl hi)).symm

lemma extend_mul_matrixTwo_support (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (i : I) (j : J) (h : (E.placement i).level ≠ q ∨ (F.placement j).level ≠ d-1) :
    (extendLayer Q E F q d f * matrixTwo Q F.differential) i j = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [extendLayer_entry]
  split_ifs with hi ht
  · have hj : (F.placement j).level ≠ (F.placement t).level - 1 := by
      rcases h with hh | hh
      · exact (hh hi).elim
      · simpa only [ht] using hh
    change f ⟨i, hi⟩ ⟨t, ht⟩ * pathTwo Q (F.differential t j) = 0
    rw [pathTwo_eq_zero Q (differential_token_level Q F hj), MulZeroClass.mul_zero]
  · exact MulZeroClass.zero_mul _
  · exact MulZeroClass.zero_mul _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
