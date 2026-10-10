import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.BlockPivot
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]
  {E : BasedComplex Q (K := K) (J ⊕ J ⊕ I)} (p : BlockPivot Q E)

lemma reduced_differential (i j : I) :
    (p.reduced Q).differential i j =
      E.differential (.inr (.inr i)) (.inr (.inr j)) -
        ∑ k : J, (p.coefficient⁻¹ • E.differential (.inr (.inr i)) (.inr (.inl k))) *
          E.differential (.inl k) (.inr (.inr j)) := by
  change (p.remainder Q * E.differential) (.inr (.inr i)) (.inr (.inr j)) = _
  rw [show p.remainder Q * E.differential = E.differential -
      E.differential * p.homotopy Q * E.differential from
    GaussianCancellation.cornerRemainder_mul_d _ _ _
      (projectiveIdentity_mul Q E.entries) E.square_zero]
  change E.differential (.inr (.inr i)) (.inr (.inr j)) -
    (∑ k, (E.differential * p.homotopy Q) (.inr (.inr i)) k *
      E.differential k (.inr (.inr j))) = _
  congr 1
  simp only [Fintype.sum_sum_type, p.mul_homotopy Q _ E.entries,
    MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.BlockPivot

end OAI
