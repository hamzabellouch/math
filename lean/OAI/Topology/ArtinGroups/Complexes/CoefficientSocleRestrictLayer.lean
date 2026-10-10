import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocle

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma coefficientSocle_restrict_layer
    (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d:ℤ) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientSocle Q E α c)
    (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ∈
      coefficientSocle Q (E.pureLayer Q hE d) α c := by
  constructor
  · intro i hi; exact hx.1 i.val hi
  · intro j a ha
    change (∑ i : {i // (E.placement i).level=d}, x i.val * (E.differential i.val j.val).arrow a)=0
    rw [← hx.2 j.val a ha]
    apply Fintype.sum_of_injective (Subtype.val : {i // (E.placement i).level=d} → I)
      Subtype.val_injective
    · intro i hi
      rw [hs i (fun h => hi ⟨⟨i,h⟩,rfl⟩),MulZeroClass.zero_mul]
    · intro i; rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
