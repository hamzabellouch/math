import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ExtendLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma differential_mul_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    E.differential * extendLayer Q E F l k f =
      extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, E.differential i t * extendLayer Q E F l k f t j) =
      ∑ t : {i // (E.placement i).level = l}, E.differential i t * f t ⟨j, hj⟩
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (E.placement t).level ≠ l := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_right hh, MulZeroClass.mul_zero]
    · intro t
      rw [extendLayer_entry, dite_eq_left t.property, dite_eq_left hj]
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs <;> exact MulZeroClass.mul_zero _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry]
    split_ifs with ht hj
    · apply tokenOnly_mul_positive Q (hE i t) _ (hf ⟨t, ht⟩ ⟨j, hj⟩).1
      apply differential_arrow_level Q E
      intro he
      exact hi (he ▸ ht)
    · exact MulZeroClass.mul_zero _
    · exact MulZeroClass.mul_zero _

lemma extendLayer_mul_differential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hF : F.IsMinimal Q) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    extendLayer Q E F l k f * F.differential =
      extendLayer Q E F l k (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, extendLayer_entry]
  split_ifs with hi hj
  · change (∑ t, extendLayer Q E F l k f i t * F.differential t j) =
      ∑ t : {j // (F.placement j).level = k}, f ⟨i, hi⟩ t * F.differential t j
    symm
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro t ht
      have hh : (F.placement t).level ≠ k := fun h => ht ⟨⟨t, h⟩, rfl⟩
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_right hh, MulZeroClass.zero_mul]
    · intro t
      rw [extendLayer_entry, dite_eq_left hi, dite_eq_left t.property]
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_left hi]
    split_ifs with ht
    · apply positive_mul_tokenOnly Q (hf ⟨i, hi⟩ ⟨t, ht⟩).1 (hF t j)
      apply differential_arrow_level Q F
      intro he
      exact hj (he.trans ht)
    · exact MulZeroClass.zero_mul _
  · apply Finset.sum_eq_zero
    intro t _
    rw [extendLayer_entry, dite_eq_right hi, MulZeroClass.zero_mul]

lemma homDifferential_extendLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) :
    homDifferential Q E F n (extendLayer Q E F l k f) = extendLayer Q E F l k
      (homDifferential Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n f) := by
  change E.differential * extendLayer Q E F l k f -
    cochainSign (K := K) n • (extendLayer Q E F l k f * F.differential) =
    extendLayer Q E F l k ((show Matrix {i // (E.placement i).level = l} {i // (E.placement i).level = l} (Q.Zigzag K) from (E.pureLayer Q hE l).differential) * f -
      cochainSign (K := K) n • (f * (show Matrix {j // (F.placement j).level = k} {j // (F.placement j).level = k} (Q.Zigzag K) from (F.pureLayer Q hF k).differential)))
  rw [map_sub, map_smul, differential_mul_extendLayer Q E F hE l k hf,
    extendLayer_mul_differential Q E F hF l k hf]

lemma extendLayer_cycle (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v)
    (hlin : LinearMatrix Q f) :
    extendLayer Q E F l k f ∈ homCycles Q E F n v := by
  refine ⟨extendLayer_homSpace Q E F hE hF l k n v hf.1, ?_⟩
  change homDifferential Q E F n (extendLayer Q E F l k f) = 0
  rw [homDifferential_extendLayer Q E F hE hF l k n hlin, hf.2, map_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
