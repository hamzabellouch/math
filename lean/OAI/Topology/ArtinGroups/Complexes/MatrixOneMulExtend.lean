import Mathlib
import OAI.Topology.ArtinGroups.Complexes.RestrictLayer
import OAI.Topology.ArtinGroups.Quivers.PathTwo

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma matrixOne_mul_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    :
    matrixOne Q E.differential * extendLayer Q E F l k f =
      extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, pathOne Q (E.differential i t) * extendLayer Q E F l k f t j) =
      ∑ t : {i // (E.placement i).level = l}, E.differential i t * f t ⟨j, hj⟩
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (E.placement t).level ≠ l := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_right hh, MulZeroClass.mul_zero]
    · intro t
      rw [extendLayer_entry, dite_eq_left t.property, dite_eq_left hj]
      exact congrArg (fun z : Q.Zigzag K => z * f t ⟨j, hj⟩)
        (pathOne_eq_self Q (E.pureLayer_linear Q hE l ⟨i, hi⟩ t).1
          (E.pureLayer_linear Q hE l ⟨i, hi⟩ t).2).symm
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs <;> exact MulZeroClass.mul_zero _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs with ht hj
    · have hz := differential_arrow_level Q E (i := i) (j := t) (fun he => hi (he ▸ ht))
      change pathOne Q (E.differential i t) * f ⟨t, ht⟩ ⟨j, hj⟩ = 0
      rw [pathOne_eq_zero Q hz, MulZeroClass.zero_mul]
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _

lemma extendLayer_mul_matrixOne (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    :
    extendLayer Q E F l k f * matrixOne Q F.differential =
      extendLayer Q E F l k (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, extendLayer Q E F l k f i t * pathOne Q (F.differential t j)) =
      ∑ t : {j // (F.placement j).level = k}, f ⟨i, hi⟩ t * F.differential t j
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (F.placement t).level ≠ k := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_right hh, MulZeroClass.zero_mul]
    · intro t
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_left t.property]
      exact congrArg (fun z : Q.Zigzag K => f ⟨i, hi⟩ t * z)
        (pathOne_eq_self Q (F.pureLayer_linear Q hF k t ⟨j, hj⟩).1
          (F.pureLayer_linear Q hF k t ⟨j, hj⟩).2).symm
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_left hi]
    split_ifs with ht
    · have hz := differential_arrow_level Q F (i := t) (j := j) (fun he => hj (he.trans ht))
      change f ⟨i, hi⟩ ⟨t, ht⟩ * pathOne Q (F.differential t j) = 0
      rw [pathOne_eq_zero Q hz, MulZeroClass.mul_zero]
    · exact MulZeroClass.zero_mul _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_right hi, MulZeroClass.zero_mul]

lemma linearHomDifferential_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)) :
    linearHomDifferential Q E F n (extendLayer Q E F l k f) = extendLayer Q E F l k
      (homDifferential Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n f) := by
  change matrixOne Q E.differential * extendLayer Q E F l k f -
    cochainSign (K := K) n • (extendLayer Q E F l k f * matrixOne Q F.differential) =
    extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f -
      cochainSign (K := K) n • (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)))
  rw [map_sub, map_smul, matrixOne_mul_extendLayer Q E F hE, extendLayer_mul_matrixOne Q E F hF]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
