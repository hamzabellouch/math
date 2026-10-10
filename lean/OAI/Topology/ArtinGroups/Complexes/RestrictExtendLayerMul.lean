import Mathlib
import OAI.Topology.ArtinGroups.Complexes.SecondaryLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma restrict_extendLayer_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d k : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K))
    (g : Matrix J J (Q.Zigzag K)) :
    restrictLayer Q E F q k (extendLayer Q E F q d f * g) =
      f * restrictLayer Q F F d k g := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ t, extendLayer Q E F q d f i.val t * g t j.val) =
    ∑ t : {j // (F.placement j).level = d}, f i t * g t.val j.val
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro t ht
    have hh : (F.placement t).level ≠ d := fun h => ht ⟨⟨t, h⟩, rfl⟩
    rw [extendLayer_entry, dite_eq_left i.property, dite_eq_right hh, MulZeroClass.zero_mul]
  · intro t
    rw [extendLayer_apply Q E F q d f i t]

lemma secondaryLayer_eq_target (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n : ℤ) (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    secondaryLayer Q E F q d n f = -(cochainSign (K := K) n •
      (f * restrictLayer Q F F d (d-1) (matrixTwo Q F.differential))) := by
  change restrictLayer Q E F q (d-1)
    (tokenHomDifferential Q E F n (extendLayer Q E F q d f)) = _
  rw [tokenHomDifferential_apply Q E F hE hF,
    capped_matrixTwo_mul_extend Q E F U q d hcap hs, zero_sub,
    map_neg, map_smul, restrict_extendLayer_mul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
