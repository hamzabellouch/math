import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I]

lemma coefficientTopDual_restrict_layer
    (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d:ℤ) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c)
    (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ∈
      coefficientTopDual Q (E.pureLayer Q hE d) α c := by
  constructor
  · intro i hi; exact hx.1 i.val hi
  · intro i a
    change (∑ j : {i // (E.placement i).level=d}, (E.differential i.val j.val).arrow a * x j.val)=0
    rw [← hx.2 i.val a]
    apply Fintype.sum_of_injective (Subtype.val : {i // (E.placement i).level=d} → I)
      Subtype.val_injective
    · intro j hj
      rw [hs j (fun h => hj ⟨⟨j,h⟩,rfl⟩),MulZeroClass.mul_zero]
    · intro j; rfl

lemma coefficientTopDual_restrict_layer_ne_zero
    (E : BasedComplex Q (K := K) I) (d:ℤ) {x : I → K}
    (hx : x≠0) (hs : ∀ i, (E.placement i).level≠d → x i=0) :
    (fun i : {i // (E.placement i).level=d} => x i.val) ≠ 0 := by
  intro hz
  apply hx
  funext i
  by_cases hi : (E.placement i).level=d
  · exact congrFun hz ⟨i,hi⟩
  · exact hs i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
